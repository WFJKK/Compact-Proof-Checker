import Lean
import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.CountedOps

set_option linter.style.longLine false

/-!
# The `acceptcheck` program: the open lane's trusted check

The acceptance service (scripts/accept.py) compiles a candidate's modules with `lean` in a box, then runs
this program, which never elaborates candidate source. It trusts the toolchain, the `.olean` files of the
trusted modules (CompactCheck, its dependencies and the generated `Protected` module), and the kernel.

    acceptcheck check <target const> <candidate const> <trusted modules...> -- <candidate .olean files...>

Imports the trusted modules, replays every constant of the candidate's `.olean` files through the kernel
(`Lean.Kernel.Environment.replay`, as lean4checker does: every definition and theorem is type-checked again,
in a fresh environment, so nothing the candidate's compilation produced is trusted), then asks the kernel to
accept the theorem `Challenge.proof : <target const> := <candidate const>`. That succeeds exactly when the
candidate's constant has the target's type. The last line of output is a JSON object:

    {"status": "accepted" | "rejected", "reason": ..., "axioms": [...], "replayed": n}

`axioms` are the axioms the challenge depends on; the service allows only `propext`, `Classical.choice` and
`Quot.sound`. `sorryAx` and `Lean.ofReduceBool` (native_decide) are among what it rejects.

    acceptcheck score <protected module> <checker> <sound> <instance> <claimed count> <claimed bill>
                      <trusted modules...> -- <candidate .olean files...>
    acceptcheck score-planned <the same arguments>

`score-planned` is the same for a planned checker `D : List Nat → Checker`: the soundness shape quantifies over
every plan `p` as well (`CostM.exec (D p Interp.counting) ⟨w, c⟩`), the instance runs `D` on the protected
module's `plan`, and the general layer may not mention that `plan`, so the plan steers the checker but is never
trusted.

The scored path (docs/COUNTED.md): after the same replay, asks the kernel to accept two theorems whose
statements this program builds itself, `Challenge.sound` at the fixed soundness shape of the checker
`D = <checker> : Checker` (for all weights `w`, certificates `c`, counts `n` and bills `cost`: if
`CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost)` then `n ≤ numCorrect graph w task`), proved by
`<sound>`, and `Challenge.instance`, `CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (<claimed
count>, <claimed bill>)`, proved by `<instance>`. The general layer (the checker, its soundness proof and
everything they depend on) may use the protected module's `graph` and `task` but no other protected
constant; it is replayed first and timed on its own. The literal weight is measured over the checker's
computational closure (its definitions, through definitions only), bodies, no exemption by name. The last line is
`{"status": "accepted" | "rejected", "reason": ..., "axioms": [...], "replayed": n,
  "general": {"constants": k, "literals": l, "kernel_ms": ms}, "rest": {...}, "challenge_ms": ms}`.

    acceptcheck lemma <theorem> <trusted modules...> -- <candidate .olean files...>

An auxiliary submission: after the same replay, checks that `<theorem>` is a theorem whose statement is a
proposition (by the kernel) and lists its axioms. The last line is `{"status", "reason", "statement",
"axioms", "replayed"}`. No target is involved: the lemma proves whatever it states.

    acceptcheck closure <checker const> <allowlist file> <protected module> <trusted modules...> -- <candidate .olean files...>

Walks the constants the checker uses, transitively through the candidate's own definitions (not into
theorems, which compute nothing), and lists every other constant that is not on the allowlist; the
protected module's `graph` and `task` are allowed, its weights and certificate are not. The last line is
`{"status": "ok" | "refused", "offending": [...], "visited": n, "checker_constants": k, "description_size": s,
"size_by": {...}}`. This is the check that a scored checker touches numbers only through the counted
primitives (docs/COUNTED.md); the description size is measured as `score` measures it, so that a development
compile can report both before a submission (`accept.py compile --checker`).

    acceptcheck protected <network.json> <protected module> <protected .olean>

Checks that the constants of a generated `Protected` module are the network of the file: the file is read
with the checker's own reader (parseNetwork in Json.lean) and compared with the module's `graph`, `weights`
and `task`. The last line is `{"status": "ok"}` or `{"status": "mismatch", "reason": ...}`.
-/

open Lean

namespace Accept

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms a constant depends on, found by walking the constants it uses. -/
partial def axiomsOf (env : Kernel.Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut stack : List Name := [root]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      match env.find? n with
      | none => continue
      | some ci =>
        if ci matches .axiomInfo _ then axioms := axioms.push n
        for m in ci.getUsedConstantsAsSet.toList do
          if !visited.contains m then stack := m :: stack
  return axioms.qsort Name.lt

def jsonOut (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj fields).compress

def rejected (reason : String) : IO UInt32 := do
  jsonOut [("status", "rejected"), ("reason", reason)]
  return 0

/-- The constants of an `.olean` file, by name. -/
def oleanConstants (path : System.FilePath) : IO (Array ConstantInfo) := do
  let (data, _region) ← readModuleData path
  return data.constants

/-- A candidate constant that the trusted modules already have, identically: a theorem with the same universe
    parameters and the same statement. Lean generates some theorems on demand, in whichever module first needs
    them: the equation lemmas `f.eq_1`, `f.eq_def` of a definition that a proof unfolds (`simp [f]`, `unfold f`,
    `rw [f]`). A candidate module that unfolds a trusted definition without importing a trusted module that
    already generated them carries its own copy. The copy changes nothing: the trusted one is kernel-checked and
    states the same, and the candidate's constants refer to it by name. It is left out of the replay; any other
    constant with a trusted name is still refused. -/
def sameTrustedTheorem (kenv : Kernel.Environment) (ci : ConstantInfo) : Bool :=
  match kenv.find? ci.name, ci with
  | some (.thmInfo t), .thmInfo c => t.levelParams == c.levelParams && t.type == c.type
  | _, _ => false

def runCheck (target cand : Name) (trusted : List Name) (oleans : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := trusted.toArray.map fun m => { module := m : Import }
  let env ← importModules imports {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  if kenv.find? target |>.isNone then
    return ← rejected s!"the target {target} is not a constant of the trusted modules"
  -- the candidate's constants, replayed through the kernel
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut count : Nat := 0
  for path in oleans do
    for ci in ← oleanConstants path do
      if (kenv.find? ci.name).isSome then
        if sameTrustedTheorem kenv ci then continue
        return ← rejected s!"the candidate redeclares {ci.name}, a constant of the trusted modules"
      if ci.name.getRoot == `Challenge then
        return ← rejected s!"the candidate declares {ci.name}; the Challenge namespace is the service's"
      if newConstants.contains ci.name then
        return ← rejected s!"the candidate declares {ci.name} twice"
      newConstants := newConstants.insert ci.name ci
      count := count + 1
  let kenv ← try Kernel.Environment.replay newConstants kenv
    catch e => return ← rejected s!"the kernel rejects the candidate: {e}"
  if (kenv.find? cand).isNone then
    return ← rejected s!"the candidate has no constant {cand}"
  -- the challenge: the candidate's constant has the target's type
  let decl := Declaration.thmDecl {
    name := `Challenge.proof, levelParams := [], type := mkConst target, value := mkConst cand }
  match kenv.addDeclCore 0 0 decl (cancelTk? := none) with
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    return ← rejected s!"the kernel rejects Challenge.proof : {target} := {cand}: {msg}"
  | .ok kenv' =>
    let axioms := axiomsOf kenv' `Challenge.proof
    jsonOut [("status", "accepted"), ("reason", Json.null),
      ("axioms", Json.arr (axioms.map fun a => Json.str a.toString)), ("replayed", Lean.toJson count)]
    return 0

/-! ## The scored path: the soundness shape, the instance, and the general-layer measures -/

def natT : Expr := mkConst ``Nat
def costT : Expr := mkConst ``CompactCheck.Cost
def certT : Expr := mkConst ``CompactCheck.Cert
def weightsT : Expr := mkApp (mkConst ``CompactCheck.Weights) (mkConst ``Rat)
def prodT (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
def optionT (a : Expr) : Expr := mkApp (mkConst ``Option [Level.zero]) a
def someE (a v : Expr) : Expr := mkApp2 (mkConst ``Option.some [Level.zero]) a v
def pairE (a b x y : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) a b x y
def eqE (ty a b : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) ty a b
def envE (w c : Expr) : Expr := mkApp2 (mkConst ``CompactCheck.Env.mk) w c

/-- The checker run by the counting interpreter: `D Interp.counting : CostM Nat`. -/
def counted (D : Name) : Expr := mkApp (mkConst D) (mkConst ``CompactCheck.Interp.counting)

/-- The soundness shape of a checker `D : Checker`:
    `∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
      CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task`. -/
def soundType (D graph task : Name) : Expr :=
  -- inside the hypothesis: w = bvar 3, c = bvar 2, n = bvar 1, cost = bvar 0
  let hyp := eqE (optionT (prodT natT costT))
    (mkApp3 (mkConst ``CompactCheck.CostM.exec) natT (counted D) (envE (mkBVar 3) (mkBVar 2)))
    (someE (prodT natT costT) (pairE natT costT (mkBVar 1) (mkBVar 0)))
  -- inside the conclusion: w = bvar 4, c = bvar 3, n = bvar 2, cost = bvar 1, h = bvar 0
  let concl := mkApp4 (mkConst ``LE.le [Level.zero]) natT (mkConst ``instLENat) (mkBVar 2)
    (mkApp3 (mkConst ``CompactCheck.numCorrect) (mkConst graph) (mkBVar 4) (mkConst task))
  mkForall `w .default weightsT (mkForall `c .default certT (mkForall `n .default natT
    (mkForall `cost .default costT (mkForall `h .default hyp concl))))

/-- The instance: `CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (n, bill)`. -/
def instanceType (D weights cert : Name) (n bill : Nat) : Expr :=
  eqE (optionT (prodT natT natT))
    (mkApp3 (mkConst ``CompactCheck.CostM.billed) natT (counted D) (envE (mkConst weights) (mkConst cert)))
    (someE (prodT natT natT) (pairE natT natT (mkNatLit n) (mkNatLit bill)))

/-! A planned checker `D : List Nat → Checker` takes a plan: whole numbers that steer it (which inputs to group,
where a loop stops), read for free as Lean data, never through the interpreter. The plan is not trusted: the
soundness shape quantifies over every plan, and the general layer may not mention the protected module's `plan`
(`generalMayUse`); only the instance runs `D` on it. -/

def listNatT : Expr := mkApp (mkConst ``List [Level.zero]) natT

/-- A planned checker on the plan `p`, run by the counting interpreter: `D p Interp.counting : CostM Nat`. -/
def countedPlanned (D : Name) (p : Expr) : Expr := mkApp2 (mkConst D) p (mkConst ``CompactCheck.Interp.counting)

/-- The soundness shape of a planned checker, for every plan:
    `∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
      CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task`. -/
def soundTypePlanned (D graph task : Name) : Expr :=
  -- inside the hypothesis: p = bvar 4, w = bvar 3, c = bvar 2, n = bvar 1, cost = bvar 0
  let hyp := eqE (optionT (prodT natT costT))
    (mkApp3 (mkConst ``CompactCheck.CostM.exec) natT (countedPlanned D (mkBVar 4)) (envE (mkBVar 3) (mkBVar 2)))
    (someE (prodT natT costT) (pairE natT costT (mkBVar 1) (mkBVar 0)))
  -- inside the conclusion: p = bvar 5, w = bvar 4, c = bvar 3, n = bvar 2, cost = bvar 1, h = bvar 0
  let concl := mkApp4 (mkConst ``LE.le [Level.zero]) natT (mkConst ``instLENat) (mkBVar 2)
    (mkApp3 (mkConst ``CompactCheck.numCorrect) (mkConst graph) (mkBVar 4) (mkConst task))
  mkForall `p .default listNatT (mkForall `w .default weightsT (mkForall `c .default certT (mkForall `n .default natT
    (mkForall `cost .default costT (mkForall `h .default hyp concl)))))

/-- The planned instance: `CostM.billed (D plan Interp.counting) ⟨weights, cert⟩ = some (n, bill)`, on the
    protected module's plan. -/
def instanceTypePlanned (D weights cert plan : Name) (n bill : Nat) : Expr :=
  eqE (optionT (prodT natT natT))
    (mkApp3 (mkConst ``CompactCheck.CostM.billed) natT (countedPlanned D (mkConst plan)) (envE (mkConst weights) (mkConst cert)))
    (someE (prodT natT natT) (pairE natT natT (mkNatLit n) (mkNatLit bill)))

/-- The candidate's constants, by name: `none` with a reason if one is a trusted constant's name (other than an
    identical copy of a trusted theorem, `sameTrustedTheorem`, which is left out), is in the `Challenge`
    namespace, or is declared twice. -/
def candidateConstants (kenv : Kernel.Environment) (oleans : List String) :
    IO (Except String (Std.HashMap Name ConstantInfo)) := do
  let mut cs : Std.HashMap Name ConstantInfo := {}
  for path in oleans do
    for ci in ← oleanConstants path do
      if (kenv.find? ci.name).isSome then
        if sameTrustedTheorem kenv ci then continue
        return .error s!"the candidate redeclares {ci.name}, a constant of the trusted modules"
      if ci.name.getRoot == `Challenge then
        return .error s!"the candidate declares {ci.name}; the Challenge namespace is the service's"
      if cs.contains ci.name then
        return .error s!"the candidate declares {ci.name} twice"
      cs := cs.insert ci.name ci
  return .ok cs

/-! ## An auxiliary lemma: replayed, a proposition, its axioms listed -/

def runLemma (cand : Name) (trusted : List Name) (oleans : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (trusted.toArray.map fun m => { module := m : Import }) {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  let cs ← match ← candidateConstants kenv oleans with
    | .ok cs => pure cs
    | .error e => return ← rejected e
  let kenv ← try Kernel.Environment.replay cs kenv
    catch e => return ← rejected s!"the kernel rejects the candidate: {e}"
  let some ci := kenv.find? cand | return ← rejected s!"the candidate has no constant {cand}"
  unless ci matches .thmInfo _ do
    return ← rejected s!"{cand} is not a theorem"
  -- its statement is a proposition, by the kernel (so a `theorem` of a data type is not a lemma)
  let isProp := match Kernel.check (Environment.ofKernelEnv kenv) {} ci.type with
    | .ok sort => match Kernel.whnf (Environment.ofKernelEnv kenv) {} sort with
      | .ok (.sort u) => u.isZero
      | _ => false
    | .error _ => false
  unless isProp do
    return ← rejected s!"the statement of {cand} is not a proposition"
  let axioms := axiomsOf kenv cand
  jsonOut [("status", "accepted"), ("reason", Json.null), ("statement", toString ci.type),
    ("axioms", Json.arr (axioms.map fun a => Json.str a.toString)), ("replayed", Lean.toJson cs.size)]
  return 0

/-- The constants of the candidate that `roots` use, transitively through the candidate's constants
    (theorems included: this is a dependency closure, not the computational one of `runClosure`),
    completed so that every inductive type comes with its whole mutual block, constructors and recursors,
    as `Kernel.Environment.replay` needs them together. -/
partial def dependencyClosure (cs : Std.HashMap Name ConstantInfo) (roots : List Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := roots
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      let some ci := cs.get? n | continue
      visited := visited.insert n
      for m in ci.getUsedConstantsAsSet.toList do
        if !visited.contains m && cs.contains m then stack := m :: stack
      -- the inductive block
      let block : List Name := match ci with
        | .inductInfo info => info.all
        | .ctorInfo info => [info.induct]
        | .recInfo info => info.all
        | _ => []
      for i in block do
        if let some (.inductInfo info) := cs.get? i then
          for m in i :: info.ctors do
            if !visited.contains m then stack := m :: stack
          -- the recursors of the block are the candidate's recInfo constants pointing at it
          for (r, rci) in cs.toList do
            if let .recInfo rinfo := rci then
              if rinfo.all.contains i && !visited.contains r then stack := r :: stack
  return visited

/-- The description size of an expression: every node counts 1 (an application, a binder, a constant, a
    variable), a natural number literal 1 per bit, a string literal 8 per byte (1 per bit), so that a
    number of `b` bits costs at least `b` however it is written (a numeral or a string: `b`; a list of
    booleans or a Church numeral: at least `2 b`, one node per bit and one per constructor or application);
    a numeral `OfNat.ofNat _ n _` is counted once. A table can live in literals, in constructors, or in
    the shape of applications alone (`fun c0 c1 z => c0 (c1 (c0 z))` carries bits), so the whole term is
    measured, as a tree: a subterm that occurs twice counts twice (the cache below only saves recomputing
    it), which is at least the length of any description of it. This bounds the description length of the
    general layer's data; it does not show the absence of compressed information. -/
partial def descSize (e : Expr) : Nat :=
  go e |>.run' {}
where
  go (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some n := (← get).get? e then return n
    let n ← match e with
      | .lit (.natVal n) => pure (max 1 (Nat.log2 n + 1))
      | .lit (.strVal s) => pure (max 1 (8 * s.utf8ByteSize))
      | .app .. =>
        let f := e.getAppFn
        let args := e.getAppArgs
        if f.isConstOf ``OfNat.ofNat && args.size == 3 then
          pure (1 + (← go args[1]!))
        else
          let mut s ← go f
          for a in args do s := s + 1 + (← go a)
          pure s
      | .lam _ ty b _ => pure (1 + (← go ty) + (← go b))
      | .forallE _ ty b _ => pure (1 + (← go ty) + (← go b))
      | .letE _ ty v b _ => pure (1 + (← go ty) + (← go v) + (← go b))
      | .mdata _ b => go b
      | .proj _ _ b => pure (1 + (← go b))
      | _ => pure 1
    modify (·.insert e n)
    return n

/-- The computational closure of the checker: the candidate's definitions it uses, transitively, through
    definitions and never through theorems (a proof computes nothing). What the checker computes is a
    function of these bodies and of the interpreter, so this is where free data could steer it, and the
    description-size budget is measured here: over the bodies, with no exemption by name (a name is the
    author's to choose). -/
partial def computationalClosure (cs : Std.HashMap Name ConstantInfo) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      let some ci := cs.get? n | continue
      if ci matches .thmInfo _ then continue
      visited := visited.insert n
      for m in ci.getUsedConstantsAsSet.toList do
        if !visited.contains m && cs.contains m then stack := m :: stack
  return visited

/-- The description size of a definition: its body. -/
def bodyLitWeight (ci : ConstantInfo) : Nat :=
  match ci.value? with | some v => descSize v | none => 0

/-- Replay a set of the candidate's constants into the kernel environment, timed. -/
def replayTimed (kenv : Kernel.Environment) (cs : Std.HashMap Name ConstantInfo) :
    IO (Except String (Kernel.Environment × Nat)) := do
  let t0 ← IO.monoMsNow
  try
    let kenv' ← Kernel.Environment.replay cs kenv
    return .ok (kenv', (← IO.monoMsNow) - t0)
  catch e => return .error s!"the kernel rejects the candidate: {e}"

/-- Ask the kernel to accept `name : type := value`. -/
def challenge (kenv : Kernel.Environment) (name : Name) (type : Expr) (value : Name) :
    IO (Except String Kernel.Environment) := do
  if (kenv.find? value).isNone then return .error s!"the candidate has no constant {value}"
  let decl := Declaration.thmDecl { name, levelParams := [], type, value := mkConst value }
  match kenv.addDeclCore 0 0 decl (cancelTk? := none) with
  | .error e => return .error s!"the kernel rejects {name} := {value}: {← (e.toMessageData {}).toString}"
  | .ok kenv' => return .ok kenv'

/-- The protected constants the general layer may use: the graph and the task (the statement of
    soundness mentions them); not the weights, the certificate, the claim or the target. -/
def generalMayUse (prot : Name) (n : Name) : Bool :=
  !(prot.isPrefixOf n) || n == prot ++ `graph || n == prot ++ `task

def runScore (prot D sound inst : Name) (n bill : Nat) (trusted : List Name) (oleans : List String)
    (planned : Bool := false) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (trusted.toArray.map fun m => { module := m : Import }) {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  for c in [prot ++ `graph, prot ++ `weights, prot ++ `task, prot ++ `cert] ++ (if planned then [prot ++ `plan] else []) do
    if (kenv.find? c).isNone then
      return ← rejected s!"the protected module has no constant {c}"
  let cs ← match ← candidateConstants kenv oleans with
    | .ok cs => pure cs
    | .error e => return ← rejected e
  for c in [D, sound, inst] do
    if !cs.contains c then return ← rejected s!"the candidate has no constant {c}"
  -- the general layer: the checker and its soundness proof, with everything they depend on
  let general := dependencyClosure cs [D, sound]
  for g in general do
    let some ci := cs.get? g | continue
    for m in ci.getUsedConstantsAsSet.toList do
      if !generalMayUse prot m then
        return ← rejected s!"the general layer ({g}) uses the protected constant {m}; only {prot}.graph and {prot}.task may appear outside the instance"
  let generalMap : Std.HashMap Name ConstantInfo := general.foldl (fun m g => match cs.get? g with
    | some ci => m.insert g ci | none => m) {}
  let restMap : Std.HashMap Name ConstantInfo := cs.fold (fun m k v => if general.contains k then m else m.insert k v) {}
  let (kenv, generalMs) ← match ← replayTimed kenv generalMap with
    | .ok r => pure r
    | .error e => return ← rejected e
  let comp := computationalClosure cs D
  let mut lits : Nat := 0
  let mut litsBy : Array (String × Json) := #[]
  for g in comp do
    let some ci := cs.get? g | continue
    let w := bodyLitWeight ci
    lits := lits + w
    if w > 0 then litsBy := litsBy.push (g.toString, Lean.toJson w)
  let (kenv, restMs) ← match ← replayTimed kenv restMap with
    | .ok r => pure r
    | .error e => return ← rejected e
  let t0 ← IO.monoMsNow
  let soundT := if planned then soundTypePlanned D (prot ++ `graph) (prot ++ `task) else soundType D (prot ++ `graph) (prot ++ `task)
  let instT := if planned then instanceTypePlanned D (prot ++ `weights) (prot ++ `cert) (prot ++ `plan) n bill
    else instanceType D (prot ++ `weights) (prot ++ `cert) n bill
  let kenv ← match ← challenge kenv `Challenge.sound soundT sound with
    | .ok k => pure k
    | .error e => return ← rejected e
  let kenv ← match ← challenge kenv `Challenge.instance instT inst with
    | .ok k => pure k
    | .error e => return ← rejected e
  let challengeMs := (← IO.monoMsNow) - t0
  let axioms := (axiomsOf kenv `Challenge.sound ++ axiomsOf kenv `Challenge.instance).toList.eraseDups.toArray.qsort Name.lt
  jsonOut [("status", "accepted"), ("reason", Json.null),
    ("axioms", Json.arr (axioms.map fun a => Json.str a.toString)), ("replayed", Lean.toJson cs.size),
    ("general", Json.mkObj [("constants", Lean.toJson general.size), ("checker_constants", Lean.toJson comp.size),
      ("description_size", Lean.toJson lits), ("size_by", Json.mkObj litsBy.toList), ("kernel_ms", Lean.toJson generalMs)]),
    ("rest", Json.mkObj [("constants", Lean.toJson restMap.size), ("kernel_ms", Lean.toJson restMs)]),
    ("challenge_ms", Lean.toJson challengeMs)]
  return 0

/-! ## The description size of a checker, for calibration and for a candidate's own development -/

def runSize (D : Name) (trusted : List Name) (oleans : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (trusted.toArray.map fun m => { module := m : Import }) {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  let cs ← match ← candidateConstants kenv oleans with
    | .ok cs => pure cs
    | .error e => return ← rejected e
  let comp := computationalClosure cs D
  let mut total : Nat := 0
  let mut by_ : Array (String × Json) := #[]
  for g in comp do
    let some ci := cs.get? g | continue
    let w := bodyLitWeight ci
    total := total + w
    by_ := by_.push (g.toString, Lean.toJson w)
  jsonOut [("status", "ok"), ("size", Lean.toJson total), ("constants", Lean.toJson comp.size), ("by", Json.mkObj by_.toList)]
  return 0

/-! ## The closure of a checker against the allowlist -/

/-- The structures projected in `e` by a primitive projection (`Expr.proj`, which names no projection
    function), with the field index: `I.ginterval` written as such is a constant to check, but an elaborator
    can build the same access as `Expr.proj CompactCheck.Interp i I`, and the closure check must see that too. -/
partial def primitiveProjections (e : Expr) (acc : Array (Name × Nat) := #[]) : Array (Name × Nat) :=
  match e with
  | .proj s i b => primitiveProjections b (acc.push (s, i))
  | .app f a => primitiveProjections a (primitiveProjections f acc)
  | .lam _ t b _ | .forallE _ t b _ => primitiveProjections b (primitiveProjections t acc)
  | .letE _ t v b _ => primitiveProjections b (primitiveProjections v (primitiveProjections t acc))
  | .mdata _ b => primitiveProjections b acc
  | _ => acc

def runClosure (root : Name) (allowPath : String) (prot : Name) (trusted : List Name) (oleans : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := trusted.toArray.map fun m => { module := m : Import }
  let env ← importModules imports {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  let allow : NameSet := (← IO.FS.lines allowPath).foldl (fun s (line : String) =>
    let l : String := line.toSlice.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then s else s.insert l.toName) {}
  let mut cand : Std.HashMap Name ConstantInfo := {}
  for path in oleans do
    for ci in ← oleanConstants path do
      cand := cand.insert ci.name ci
  let mut visited : NameSet := {}
  let mut offending : Array Name := #[]
  let mut stack : List Name := [root]
  if !cand.contains root then
    jsonOut [("status", "refused"), ("offending", Json.arr #[Json.str root.toString]),
      ("reason", s!"{root} is not a constant of the candidate")]
    return 0
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      match cand.get? n with
      | some ci =>
        -- the candidate's own constant: a proof computes nothing; a definition is followed
        if ci matches .thmInfo _ then continue
        for m in ci.getUsedConstantsAsSet.toList do
          if !visited.contains m then stack := m :: stack
        -- a primitive projection of a trusted structure counts as its projection function (the field's name)
        for (st, i) in primitiveProjections ci.type ++ (ci.value?.map primitiveProjections |>.getD #[]) do
          if cand.contains st then continue
          match (getStructureFields env st)[i]? with
          | some f =>
            let n := st ++ f
            if !visited.contains n then stack := n :: stack
          | none => offending := offending.push (st ++ Name.mkSimple s!"proj{i}")
      | none =>
        match kenv.find? n with
        | some (.thmInfo _) => continue
        | _ =>
          if !allow.contains n && n != prot ++ `graph && n != prot ++ `task then
            offending := offending.push n
  let sorted := offending.qsort Name.lt
  -- the description size, measured as `score` measures it (the same closure and the same weights), so that a
  -- development compile can show it before a submission
  let comp := computationalClosure cand root
  let mut lits : Nat := 0
  let mut litsBy : Array (String × Json) := #[]
  for g in comp do
    let some ci := cand.get? g | continue
    let w := bodyLitWeight ci
    lits := lits + w
    if w > 0 then litsBy := litsBy.push (g.toString, Lean.toJson w)
  jsonOut [("status", if sorted.isEmpty then "ok" else "refused"),
    ("offending", Json.arr (sorted.map fun a => Json.str a.toString)), ("visited", Lean.toJson visited.size),
    ("checker_constants", Lean.toJson comp.size), ("description_size", Lean.toJson lits),
    ("size_by", Json.mkObj litsBy.toList)]
  return 0

/-! ## The protected module against the network file -/

unsafe def evalProtected (mod : Name) :
    IO (Except String (CompactCheck.Graph × CompactCheck.Weights Rat × String × List Nat)) := do
  -- trusted modules only here (the generated module and what it imports), so their initializers may run
  enableInitializersExecution
  let env ← importModules #[{ module := mod }] {} (trustLevel := 0) (loadExts := true)
  return do
    let g ← env.evalConst CompactCheck.Graph {} (mod ++ `graph)
    let w ← env.evalConst (CompactCheck.Weights Rat) {} (mod ++ `weights)
    let t ← env.evalConst CompactCheck.Task {} (mod ++ `task)
    return (g, w, t.name, t.space)

@[implemented_by evalProtected]
opaque evalProtectedSafe (mod : Name) :
    IO (Except String (CompactCheck.Graph × CompactCheck.Weights Rat × String × List Nat))

/-- Two graphs are the same: the same sizes, operations and output. -/
def sameGraph (a b : CompactCheck.Graph) : Bool :=
  a.positions == b.positions && a.values == b.values && a.nodes == b.nodes && a.output == b.output

def runProtected (netPath : String) (mod : Name) (olean : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- the module we evaluate must be the file the service compiled
  let (data, _) ← readModuleData olean
  unless data.constants.any (·.name == mod ++ `Target) do
    jsonOut [("status", "mismatch"), ("reason", s!"{olean} does not define {mod}.Target")]
    return 0
  let net ← match CompactCheck.parseNetwork (← CompactCheck.readJson netPath) with
    | .ok n => pure n
    | .error e => do
      jsonOut [("status", "mismatch"), ("reason", s!"cannot read {netPath}: {e}")]
      return 0
  match ← evalProtectedSafe mod with
  | .error e =>
    jsonOut [("status", "mismatch"), ("reason", s!"cannot evaluate the module's constants: {e}")]
  | .ok (g, w, tname, tspace) =>
    if !sameGraph g net.graph then
      jsonOut [("status", "mismatch"), ("reason", "the graph differs from the network file's")]
    else if !(w == net.weights) then
      jsonOut [("status", "mismatch"), ("reason", "the weights differ from the network file's")]
    else if tname != net.task.name || tspace != net.task.space then
      jsonOut [("status", "mismatch"), ("reason", "the task differs from the network file's")]
    else
      jsonOut [("status", "ok"), ("network", net.network),
        ("domain", Lean.toJson (CompactCheck.shapeSize net.task.space))]
  return 0

end Accept

def usage : String :=
  "usage: acceptcheck check <target> <candidate const> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck score <protected module> <checker> <sound> <instance> <count> <bill> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck score-planned <protected module> <checker> <sound> <instance> <count> <bill> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck lemma <theorem> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck size <checker const> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck closure <checker const> <allowlist> <protected module> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck protected <network.json> <protected module> <protected olean>"

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: target :: cand :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runCheck target.toName cand.toName (trusted.map String.toName) oleans
  | "score" :: prot :: D :: sound :: inst :: n :: bill :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    match n.toNat?, bill.toNat? with
    | some n, some bill =>
      if oleans.isEmpty then
        IO.eprintln usage
        return 2
      Accept.runScore prot.toName D.toName sound.toName inst.toName n bill (trusted.map String.toName) oleans
    | _, _ =>
      IO.eprintln usage
      return 2
  | "score-planned" :: prot :: D :: sound :: inst :: n :: bill :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    match n.toNat?, bill.toNat? with
    | some n, some bill =>
      if oleans.isEmpty then
        IO.eprintln usage
        return 2
      Accept.runScore prot.toName D.toName sound.toName inst.toName n bill (trusted.map String.toName) oleans (planned := true)
    | _, _ =>
      IO.eprintln usage
      return 2
  | "size" :: D :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runSize D.toName (trusted.map String.toName) oleans
  | "closure" :: root :: allow :: prot :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runClosure root.toName allow prot.toName (trusted.map String.toName) oleans
  | "lemma" :: cand :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runLemma cand.toName (trusted.map String.toName) oleans
  | ["protected", net, mod, olean] => Accept.runProtected net mod.toName olean
  | _ =>
    IO.eprintln usage
    return 2

import CompactCheck.Json
import CompactCheck.Semantics
import CompactCheck.CountedCheck
import CompactCheck.CountedGeneral
import CompactCheck.Tokens
import CompactCheck.TokensCost

/-!
# The `compactcheck` program

    compactcheck <network.json> <proof.json>
        Check a proof. The last line is {"certified": n}, as the pipeline's
        lean_check hook expects; a rejected proof gives n = 0 and a reason.

    compactcheck brute <network.json>
        Check every input on its own: the number the single-input test
        certifies, and a mask with one 0 or 1 per input, in the order of
        itertools.product over the input space. Exact for linear networks;
        for general networks with the bounds of `General.lean`.

    compactcheck logits <network.json> <inputs.json>
        The exact logits for each input in a JSON list of token lists, as
        fractions. For comparing with PyTorch and the Python checker. Linear
        networks only.

    compactcheck leaves <network.json> <proof.json>
        The outcome of every leaf of the proof's split tree, in the tree's
        order: its box, its rule, and whether it is certified. For comparing
        with the Python checker leaf by leaf.

    compactcheck cost <network.json> <proof.json>
        Check a proof and bill it under cost-v3 (CountedCheck.lean): the last
        line is {"certified": n, "length": total, "by_category": {...}}, or
        {"status": "rejected", "reason": ...}. Linear networks only, for now.

    compactcheck gsingle <network.json> <inputs.json>
        The open lane's single rule for general networks (`CostM.gsingle`,
        CountedGeneral.lean) on each input of a JSON list of token lists:
        the verdict and the cost-v3 charge, one JSON object per line. For
        comparing the charge with the Python checker's single leaf.

    compactcheck ginterval <network.json> <boxes.json>
        The interval rule for general networks (`CostM.ginterval`) on each box
        of a JSON list (a box: one [lo, hi] per position): the verdict and the
        cost-v3 charge, one JSON object per line.

    compactcheck tokens <network.json> <leaves.json>
        For each box and label in a JSON list of {"ranges": [[lo, hi], ...],
        "label": l}: the lowest margin bound of a token_interval leaf, as
        [m, e] for m * 2^e (null if the network has one output), or
        "error" where the proof would be rejected. For comparing with the
        Python checker bound for bound.

    compactcheck gtokens <network.json> <boxes.json>
        The token_interval rule for general networks, priced (`gtokenRun`,
        TokensCost.lean), on the boxes of a JSON list in order, as the leaves of
        one proof: per box a line with the verdict, the charge to token_interval,
        what the box added to tables (the rows that depend on their token alone,
        charged once per proof) and its requests for those rows (`reqs`, as
        `gtokenLeaf` returns them); then a line with the whole list's verdicts
        and charges. For comparing with the Python checker leaf by leaf, and for
        writing an instance proof's facts.

    compactcheck floats <network.json> <inputs.json>
        The logits for each input computed in floats with the spec's
        definitions (`semGraph` in Semantics.lean), for any network. Each
        float is printed as its 64 bits, so Python reads it exactly. For
        comparing the network Lean reads with PyTorch's.
-/

open Lean (Json)
open CompactCheck

def loadNetwork (path : String) : IO NetworkFile := do
  match parseNetwork (← readJson path) with
  | .ok net => pure net
  | .error e => throw (IO.userError s!"{path}: {e}")

def runCheck (netPath proofPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let proofJson ← readJson proofPath
  match checkProofFile net proofJson with
  | .ok n => IO.println (Json.mkObj [("certified", Lean.toJson n)]).compress
  | .error e =>
    IO.println (Json.mkObj [("certified", Lean.toJson (0 : Nat)), ("status", Json.str "rejected"),
      ("reason", Json.str e)]).compress
  return 0

def runBrute (netPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let test ← if net.general then
      match dweights net.weights with
      | some dw => pure fun x => (generalSingle net.graph dw net.task x).getD false
      | none => throw (IO.userError "a weight is not a tensor of dyadic numbers")
    else pure fun x => singleOk net.graph net.weights net.task x
  let mask := (allInputs net.task.space).map fun x => if test x then '1' else '0'
  let n := mask.count '1'
  IO.println (Json.mkObj [("correct", Lean.toJson n), ("mask", Json.str (String.ofList mask))]).compress
  return 0

def readInputs (path : String) : IO (List Input) := do
  match (← readJson path).getArr? with
  | .ok a => a.toList.mapM fun j => match Lean.fromJson? (α := List Nat) j with
    | .ok x => pure x
    | .error e => throw (IO.userError e)
  | .error e => throw (IO.userError e)

def runLogits (netPath inputsPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let inputs ← readInputs inputsPath
  let rows := inputs.map fun x =>
    match evalGraph net.graph net.weights x with
    | some out => Json.arr (out.data.map fun q => Json.str (toString q))
    | none => Json.null
  IO.println (Json.arr rows.toArray).compress
  return 0

def runGSingle (netPath inputsPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let inputs ← readInputs inputsPath
  match dweights net.weights with
  | none => throw (IO.userError "a weight is not a tensor of dyadic numbers")
  | some dw =>
    for x in inputs do
      let row := match gsingleRun net.graph dw net.task x with
        | some (b, k) => Json.mkObj [("input", Lean.toJson x), ("verdict", Lean.toJson b), ("charge", Lean.toJson k)]
        | none => Json.mkObj [("input", Lean.toJson x), ("status", Json.str "unsupported")]
      IO.println row.compress
    return 0

def readBoxes (path : String) : IO (List Box) := do
  match (← readJson path).getArr? with
  | .ok a => a.toList.mapM fun j => match Lean.fromJson? (α := List (List Nat)) j with
    | .ok rs => rs.mapM fun r => match r with
      | [lo, hi] => pure (⟨lo, hi⟩ : Range)
      | _ => throw (IO.userError "a range is [lo, hi]")
    | .error e => throw (IO.userError e)
  | .error e => throw (IO.userError e)

def runGInterval (netPath boxesPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let boxes ← readBoxes boxesPath
  match dweights net.weights with
  | none => throw (IO.userError "a weight is not a tensor of dyadic numbers")
  | some dw =>
    for b in boxes do
      let bj := Lean.toJson (b.map fun r => [r.lo, r.hi])
      let row := match gintervalRun net.graph dw net.task b with
        | some (v, k) => Json.mkObj [("box", bj), ("verdict", Lean.toJson v), ("charge", Lean.toJson k)]
        | none => Json.mkObj [("box", bj), ("status", Json.str "unsupported")]
      IO.println row.compress
    return 0

def ruleName : Rule → String
  | .single => "single"
  | .skip => "skip"
  | .interval _ => "interval"
  | .tokenInterval => "token_interval"

def runLeaves (netPath proofPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let fail (e : String) : IO UInt32 := do
    IO.println (Json.mkObj [("status", Json.str "rejected"), ("reason", Json.str e)]).compress
    return 0
  match parseProof (← readJson proofPath) net.names with
  | .error e => fail e
  | .ok proof =>
    match walk proof.tree (rootBox net.task.space) with
    | .error e => fail e
    | .ok leaves =>
      let outcome? : Except String (Leaf → Except String Bool) :=
        if net.general then
          match dweights net.weights with
          | some dw => .ok (generalLeafOk net.graph dw net.task)
          | none => .error "a weight is not a tensor of dyadic numbers"
        else do
          let (g', w') ← contractAll net.graph net.weights proof.contractions
          let approxs ← buildApproxs g' w' proof.approximations
          pure (leafOk g' w' net.task approxs)
      match outcome? with
      | .error e => fail e
      | .ok outcome =>
        let rows := leaves.map fun l =>
          let res := match outcome l with
            | .ok b => Lean.toJson b
            | .error e => Json.str ("error: " ++ e)
          Json.mkObj [("ranges", Lean.toJson (l.box.map fun r => [r.lo, r.hi])),
            ("rule", Json.str (ruleName l.rule)), ("accepted", res)]
        IO.println (Json.arr rows.toArray).compress
        return 0

instance : Zero Float := ⟨0⟩
instance : One Float := ⟨1⟩
instance : ExpDiv Float := ⟨Float.exp, (· / ·)⟩

/-- A weight as a float (numerator and denominator rounded separately). -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

def runFloats (netPath inputsPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let inputs ← readInputs inputsPath
  let w : Weights Float := net.weights.map fun p => (p.1, p.2.map ratToFloat)
  let rows := inputs.map fun x =>
    match semGraph net.graph w x with
    | some out => Json.mkObj [("shape", Lean.toJson out.shape),
        ("bits", Json.arr (out.data.map fun f => Lean.toJson f.toBits.toNat))]
    | none => Json.null
  IO.println (Json.arr rows.toArray).compress
  return 0

def runCost (netPath proofPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let proofJson ← readJson proofPath
  let fail (e : String) : IO UInt32 := do
    IO.println (Json.mkObj [("status", Json.str "rejected"), ("reason", Json.str e)]).compress
    return 0
  if net.general then return ← fail "the counted checker covers linear networks only, for now"
  let limit := maxScalars (shapeSize net.task.space)
  let nScalars := countScalars proofJson
  if nScalars > limit then return ← fail s!"the proof file has more than {limit} numbers and strings"
  match parseProof proofJson net.names with
  | .error e => fail e
  | .ok proof =>
    if proof.network != net.network then return ← fail s!"the proof names network {proof.network}, not {net.network}"
    match checkProofCounted net.graph net.weights net.task proof with
    | .error e => fail e
    | .ok (n, c) =>
      IO.println (Json.mkObj [("certified", Lean.toJson n), ("length", Lean.toJson c.total),
        ("by_category", Json.mkObj (c.map fun (k, v) => (k, Lean.toJson v)))]).compress
      return 0

def runGTokens (netPath boxesPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let boxes ← readBoxes boxesPath
  match dweights net.weights with
  | none => throw (IO.userError "a weight is not a tensor of dyadic numbers")
  | some dw =>
    let mut acc : Memo × Nat := ([], 0)
    for b in boxes do
      let bj := Lean.toJson (b.map fun r => [r.lo, r.hi])
      match gtokenLeaf net.graph dw net.task b with
      | none =>
        IO.println (Json.mkObj [("box", bj), ("status", Json.str "rejected")]).compress
        return 0
      | some (v, k, rq) =>
        let acc' := rq.foldl tablesStep acc
        let reqs := rq.map fun r => Json.mkObj [("key", Lean.toJson r.key), ("lo", Lean.toJson r.lo),
          ("hi", Lean.toJson r.hi), ("cost", Lean.toJson r.cost)]
        IO.println (Json.mkObj [("box", bj), ("verdict", Lean.toJson v), ("token_interval", Lean.toJson k),
          ("tables", Lean.toJson (acc'.2 - acc.2)), ("requests", Lean.toJson rq.length),
          ("reqs", Json.arr reqs.toArray)]).compress
        acc := acc'
    match gtokenRun net.graph dw net.task boxes with
    | some (bs, k, t) =>
      IO.println (Json.mkObj [("verdicts", Lean.toJson bs), ("token_interval", Lean.toJson k),
        ("tables", Lean.toJson t)]).compress
    | none => IO.println (Json.mkObj [("status", Json.str "rejected")]).compress
    return 0

def runTokens (netPath leavesPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let dw ← match dweights net.weights with
    | some dw => pure dw
    | none => throw (IO.userError "a weight is not a tensor of dyadic numbers")
  let leaves ← match (← readJson leavesPath).getArr? with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  let rows ← leaves.toList.mapM fun j => do
    let ranges ← match j.getObjValAs? (List (List Nat)) "ranges" with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    let label ← match j.getObjValAs? Nat "label" with
      | .ok l => pure l
      | .error e => throw (IO.userError e)
    let box : Box := ranges.map fun r => ⟨r.getD 0 0, r.getD 1 0⟩
    pure (match tokenLeafBound net.graph dw box label with
      | none => Json.str "error"
      | some none => Json.null
      | some (some (m, e)) => Json.arr #[Json.str (toString m), Lean.toJson e])
  IO.println (Json.arr rows.toArray).compress
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cost", net, proof] => runCost net proof
  | ["brute", net] => runBrute net
  | ["logits", net, inputs] => runLogits net inputs
  | ["floats", net, inputs] => runFloats net inputs
  | ["gsingle", net, inputs] => runGSingle net inputs
  | ["ginterval", net, boxes] => runGInterval net boxes
  | ["leaves", net, proof] => runLeaves net proof
  | ["tokens", net, leaves] => runTokens net leaves
  | ["gtokens", net, boxes] => runGTokens net boxes
  | [net, proof] => runCheck net proof
  | _ =>
    IO.eprintln ("usage: compactcheck <network.json> <proof.json> | brute <network.json> | " ++
      "logits <network.json> <inputs.json> | leaves <network.json> <proof.json> | " ++
      "cost <network.json> <proof.json> | tokens <network.json> <leaves.json> | " ++
      "floats <network.json> <inputs.json> | " ++
      "gsingle <network.json> <inputs.json> | ginterval <network.json> <boxes.json> | " ++
      "gtokens <network.json> <boxes.json>")
    return 2

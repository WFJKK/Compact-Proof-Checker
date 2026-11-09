import CompactCheck.Tokens
import CompactCheck.CountedGeneral

/-!
# token_interval leaves, priced as cost-v3 prices them

`Tokens.lean` checks a token_interval leaf as `core/check/tokens.py` does. This file adds what the
Python checker charges for it, so that the rule can be a counted operation of the open lane (the
maximum-knowledge condition) at exactly the fixed rules lane's price.

Python charges a token_interval leaf in two places:

- `token_interval`: the leaf's own work, operation by operation (`TokenEvaluator.charge`), and, for
  the operations the token rules do not cover, twice what the single rule charges (`_eval` with
  factor 2);
- `tables`: the rows that depend on their token alone (`pure` rows: a lookup, then constants). The
  checker keeps them for the whole proof (`TokenEvaluator.rows`, memo key and token) and charges each
  row once per proof.

`tcostOp` follows `tevalOp` step by step, computing each value with the same functions, and adds the
charges Python makes on the same path, with the bookkeeping Python keeps beside its values for the
memo (`Tag`: whether rows are pure, the node where they began, the matrix products since). Its values
are `tevalOp`'s (`tcostOp_fst`), so the verdict of a priced leaf is `generalTokenInterval`'s
(`gtokenLeaf_verdict`), whose soundness is proved in `TokensLeafSound.lean`.

A leaf's bill is its charge to `token_interval` and its requests for pure rows (`RowReq`: memo key,
tokens, price of a row). `gtokenRun` runs a list of leaves and charges the requests once per proof
(`tablesCharge`), as Python's memo does over a proof's leaves in order. Python's memo keys name nodes;
here they are node indices, and keep the same rows apart.

This file uses only core Lean.
-/

namespace CompactCheck

/-! ## What Python keeps beside a value -/

/-- Beside a `Sep` (or a `WSep`'s `Sep`): whether its rows depend on their token alone, and the node
    of the lookup where they began. -/
structure SepTag where
  pure : Bool
  origin : Nat
deriving Repr, Inhabited

/-- Beside a term of a `Mix`: whether its rows are pure, the node where the term began, and the
    nodes of the matrix products applied to its rows since, in order. -/
structure TermTag where
  pure : Bool
  origin : Nat
  chain : List Nat
deriving Repr, Inhabited

/-- The tags of a value: a `Sep` or `WSep` has its `Sep`'s, a `Mix` one per term. -/
inductive Tag where
  | none
  | sep (t : SepTag)
  | mix (ts : List TermTag)
deriving Repr, Inhabited

/-- A `Sep`'s tag; rows of unknown origin count as not pure, which is charged in full. -/
def Tag.sepTag : Tag → SepTag
  | .sep t => t
  | _ => ⟨false, 0⟩

def Tag.terms : Tag → List TermTag
  | .mix ts => ts
  | _ => []

def TermTag.default : TermTag := ⟨false, 0, []⟩

/-! ## Bills -/

/-- A request for pure rows: the memo key, the tokens `lo..hi`, and the price of one row. -/
structure RowReq where
  key : List Nat
  lo : Nat
  hi : Nat
  cost : Nat
deriving Repr, DecidableEq

/-- What a leaf costs: its own work (`token_interval`) and its requests for pure rows (`tables`,
    once per proof), oldest first. -/
structure Bill where
  leaf : Nat
  reqs : List RowReq
deriving Repr

def Bill.zero : Bill := ⟨0, []⟩

def Bill.add (a b : Bill) : Bill := ⟨a.leaf + b.leaf, a.reqs ++ b.reqs⟩

instance : Add Bill := ⟨Bill.add⟩

def Bill.ofLeaf (n : Nat) : Bill := ⟨n, []⟩

def Bill.sum (bs : List Bill) : Bill := bs.foldl (· + ·) Bill.zero

/-- 1 for an exact value, 2 for an interval (Python's `_f`). -/
def fac (exact : Bool) : Nat := if exact then 1 else 2

/-- Memo keys. Python's are `(node, origin, position)` for the rows of a `Sep`, the same with `"+"`
    for a constant added at a node, and `(node, origin, position, chain)` for a term's rows. -/
def sepKey (node origin p : Nat) : List Nat := [0, node, origin, p]
def plusKey (node origin p : Nat) : List Nat := [1, node, origin, p]
def termKey (node origin pos : Nat) (chain : List Nat) : List Nat := [2, node, origin, pos] ++ chain

/-- Python's `rows`: pure rows are requested from the proof's tables; other rows are computed and
    charged in the leaf, `cost` per token of the range. -/
def rowsBill (key : List Nat) (r : Range) (cost : Nat) (pure : Bool) : Bill :=
  if pure then ⟨0, [⟨key, r.lo, r.hi, cost⟩]⟩ else ⟨cost * (r.hi + 1 - r.lo), []⟩

/-- The leaf's range at position `p`. -/
def TCtx.range (ctx : TCtx) (p : Nat) : Range := ctx.box.getD p ⟨0, 0⟩

/-- One request per position, for a `Sep`'s rows. -/
def sepRowsBill (ctx : TCtx) (n : Nat) (key : Nat → List Nat) (cost : Nat) (pure : Bool) : Bill :=
  Bill.sum ((List.range n).map fun p => rowsBill (key p) (ctx.range p) cost pure)

/-! ## Leaving the token domain (Python's `to_var`, `collapse`, `concretize`, `leave`) -/

/-- `to_var`: a `WSep` multiplies its weights into every input's rows; a `Mix` adds its terms per
    input; a `Sep` only rearranges. -/
def toVarBill (ctx : TCtx) : TV → Nat
  | .wsep w s => ctx.k * shapeSize s.shape * fac w.exact
  | .wsepv ws s => ctx.k * shapeSize s.shape * fac (ws.all (·.exact))
  | .mix m => (m.terms.map fun t => 2 * (ctx.k * shapeSize (t.rows.shape.drop 1)) * fac t.w.exact).sum
  | _ => 0

/-- `collapse` of per-input values: their box, if there are several. -/
def collapseVarBill (vs : Array DT) : Nat :=
  if vs.size > 1 then 2 * (vs.size * shapeSize (vs.getD 0 emptyDT).shape) else 0

/-- `collapse` of a `Sep`: the box of each position's rows that has more than one. -/
def collapseSepBill (s : Sep) : Nat :=
  (s.rows.map fun r => if r.shape.headD 0 > 1 then 2 * shapeSize r.shape else 0).sum

/-- The box of a `Sep`'s rows is exact when every position has one row. -/
def Sep.boxExact (s : Sep) : Bool := s.rows.all fun r => r.shape.headD 0 == 1

/-- `collapse` of a `WSep`: the weights' box (per-input weights), the rows' box, their product. -/
def collapseWSepBill (w : Sum DT (Array DT)) (s : Sep) : Nat :=
  let wBill := match w with
    | .inl _ => 0
    | .inr ws => collapseVarBill ws
  let wExact := match w with
    | .inl w => w.exact
    | .inr ws => ws.size == 1 && ws.all (·.exact)
  wBill + collapseSepBill s + shapeSize s.shape * fac (wExact && s.boxExact)

/-- Python's `concretize` applies: an exact constant, and terms of one row and an exact scalar weight. -/
def concretizable (m : Mix) : Bool :=
  m.const.exact && m.terms.all fun t => t.rows.shape.headD 0 == 1 && t.w.exact && t.w.shape == []

def concretizeBill (m : Mix) : Nat := m.terms.length * (2 * shapeSize m.const.shape)

/-- `collapse` of a `Mix`: the exact value if it is one, else per term the box of its rows and the
    product with its weight's box. -/
def collapseMixBill (m : Mix) : Nat :=
  if concretizable m then concretizeBill m else
  (m.terms.map fun t =>
    let T := t.rows.shape.headD 0
    let wExact := t.w.shape == [] && t.w.exact
    (if T > 1 then 2 * shapeSize t.rows.shape else 0) +
      2 * shapeSize (1 :: t.rows.shape.drop 1) * fac (wExact && T == 1)).sum

/-- `leave`: what a domain value costs to become per-input values (one varying position at most)
    or an interval tensor. -/
def leaveBill (ctx : TCtx) : TV → Nat
  | .mix m =>
    if concretizable m then concretizeBill m
    else if ctx.aligned then toVarBill ctx (.mix m) else collapseMixBill m
  | .sep s => if ctx.aligned then 0 else collapseSepBill s
  | .wsep w s => if ctx.aligned then toVarBill ctx (.wsep w s) else collapseWSepBill (.inl w) s
  | .wsepv ws s => if ctx.aligned then toVarBill ctx (.wsepv ws s) else collapseWSepBill (.inr ws) s
  | _ => 0

/-- Collapsing the per-input arguments of an operation, once per node (Python collapses `env2[x]` and
    finds an interval tensor the second time a node is named). -/
def collapseVarsBill (args : List Nat) (left : List TV) : Nat :=
  let distinct := (args.zip left).foldl
    (fun acc (a, v) => if acc.any (·.1 == a) then acc else acc ++ [(a, v)]) ([] : List (Nat × TV))
  (distinct.map fun (_, v) => match v with
    | .var vs => collapseVarBill vs
    | _ => 0).sum

/-! ## Operations on per-input values (Python's `var_op`) -/

/-- Whether Python's `it(a)` is exact. -/
def TV.itExact : TV → Bool
  | .var vs => vs.all (·.exact)
  | .dt v => v.exact
  | .sep _ => true
  | .wsep w _ => w.exact
  | .wsepv ws _ => ws.all (·.exact)
  | .mix m => m.const.exact && m.terms.all (·.w.exact)
  | .box => false

/-- What `var_op` charges when it computes `out` (the arguments that are domain values become
    per-input values first, `to_var`). -/
def varOpBill (ctx : TCtx) (op : Op) (args : List TV) (out : TV) : Nat :=
  let outSize := match out with
    | .var vs => vs.size * shapeSize (vs.getD 0 emptyDT).shape
    | _ => 0
  let outExact := match out with
    | .var vs => vs.all (·.exact)
    | _ => true
  match op, args with
  | .binary _ _ _, [x, y] => toVarBill ctx x + toVarBill ctx y + outSize * fac outExact
  | .neg _, [x] => toVarBill ctx x + outSize
  | .matmul _ _, [x, .dt b] => toVarBill ctx x + outSize * b.shape.headD 0 * fac (x.itExact && b.exact)
  | .unsqueeze _ _, [x] => toVarBill ctx x
  | .sum _ d, [x] =>
    let sh := x.shape ctx
    let L := match normDim d sh.length with
      | some k => sh.getD k 1
      | none => 1
    toVarBill ctx x + outSize * (L - 1) * fac x.itExact
  | .softmax _ _, [x] => toVarBill ctx x + 6 * (ctx.k * shapeSize (x.shape ctx))
  | .exp _, [x] => toVarBill ctx x + 2 * (ctx.k * shapeSize (x.shape ctx))
  | .index _ _, [x] => toVarBill ctx x
  | _, _ => 0

/-- What Python's `evaluate` charged before it gave up on the node: `var_op` turns the left operand
    of a matrix product into per-input values before it sees that the right one is a domain value. -/
def preDeclineBill (ctx : TCtx) (op : Op) (args : List TV) : Nat :=
  match op, args with
  | .matmul _ _, [x, y] =>
    match x with
    | .box => 0
    | _ => if (x.isVar || y.isVar) && y.isDomain then toVarBill ctx x else 0
  | _, _ => 0

/-! ## The operations the token rules do not cover -/

/-- What the single rule charges for the operation (`gopCost`), from the arguments' shapes, which
    leaving the domain does not change. Python's `_eval` charges twice this in a token_interval leaf. -/
def tplainCost (g : Graph) (ctx : TCtx) (vals : Array TV) (out : DT) : Op → Nat
  | .matmul a _ =>
    if g.nodes[a]? == some .input then shapeSize out.shape
    else
      match vals[a]? with
      | some x => shapeSize out.shape * (x.shape ctx).getLast?.getD 1
      | none => shapeSize out.shape
  | .add _ _ => shapeSize out.shape
  | .binary _ _ _ => shapeSize out.shape
  | .neg _ => shapeSize out.shape
  | .sum a d =>
    match vals[a]? with
    | some x =>
      match normDim d (x.shape ctx).length with
      | some k => shapeSize out.shape * ((x.shape ctx).getD k 1 - 1)
      | none => 0
    | none => 0
  | .exp _ => shapeSize out.shape
  | .softmax _ _ => 3 * shapeSize out.shape
  | _ => 0

/-! ## The token rules -/

/-- The charge of a token rule that computed `out`, and `out`'s tag, from the node's index `self`,
    the operation, its arguments and their tags (Python's `evaluate` and the rules it calls). -/
def ruleBill (ctx : TCtx) (free : Nat → Bool) (self : Nat) (op : Op) (args : List TV)
    (tags : List Tag) (out : TV) : Bill × Tag :=
  let tag0 := tags.getD 0 .none
  let tag1 := tags.getD 1 .none
  let outConst := match out with
    | .mix o => o.const
    | _ => emptyDT
  match op, args with
  | .matmul _ _, [.box, .dt w] =>
    -- the lookup: one row of `w` per token and position, pure
    (sepRowsBill ctx ctx.box.length (fun p => sepKey self self p) (w.shape.getD 1 0) true, .sep ⟨true, self⟩)
  | .binary .mul _ _, [.var _, .sep _] => (Bill.zero, tag1)
  | .binary .mul _ _, [.sep _, .var _] => (Bill.zero, tag0)
  | op, args =>
    if args.any TV.isVar then (Bill.ofLeaf (varOpBill ctx op args out), .none) else
    match op, args with
    | .matmul _ b, [.sep s, .dt bm] =>
      let st := tag0.sepTag
      let pure := st.pure && free b
      let cost := bm.shape.getD 0 0 * bm.shape.getD 1 0
      (sepRowsBill ctx s.rows.length (fun p => sepKey self st.origin p) cost pure, .sep ⟨pure, st.origin⟩)
    | .matmul _ b, [.mix m, .dt bm] =>
      let cost := bm.shape.getD 0 0 * bm.shape.getD 1 0
      let ts := tag0.terms
      let parts := ((List.range m.terms.length).zip m.terms).map fun (j, t) =>
        let tt := ts.getD j TermTag.default
        let pure := tt.pure && free b
        (rowsBill (termKey self tt.origin t.pos tt.chain) (ctx.range t.pos) cost pure,
          (⟨pure, tt.origin, tt.chain ++ [self]⟩ : TermTag))
      let constCharge := if m.const.exact && m.const.lo.all (· == 0) then shapeSize m.const.shape
        else shapeSize outConst.shape * bm.shape.getD 0 0 * fac m.const.exact
      (Bill.sum (parts.map (·.1)) + Bill.ofLeaf constCharge, .mix (parts.map (·.2)))
    | .binary .add l r, [x, y] =>
      match x, y with
      | .mix _, .mix _ =>
        (Bill.ofLeaf (shapeSize outConst.shape * fac outConst.exact), .mix (tag0.terms ++ tag1.terms))
      | .mix _, .dt _ => (Bill.ofLeaf (shapeSize outConst.shape * fac outConst.exact), .mix tag0.terms)
      | .dt _, .mix _ => (Bill.ofLeaf (shapeSize outConst.shape * fac outConst.exact), .mix tag1.terms)
      | .sep s, .dt _ =>
        let st := tag0.sepTag
        let pure := st.pure && free r
        (sepRowsBill ctx s.rows.length (fun p => plusKey self st.origin p) (shapeSize s.rest) pure,
          .sep ⟨pure, st.origin⟩)
      | .dt _, .sep s =>
        let st := tag1.sepTag
        let pure := st.pure && free l
        (sepRowsBill ctx s.rows.length (fun p => plusKey self st.origin p) (shapeSize s.rest) pure,
          .sep ⟨pure, st.origin⟩)
      | _, _ => (Bill.zero, .none)
    | .binary .mul l r, [x, y] =>
      let (v, vtag, c, ci) := if x.isDomain then (x, tag0, y, r) else (y, tag1, x, l)
      let cExact := match c with
        | .dt c => c.exact
        | _ => false
      match v, out with
      | .mix m, _ =>
        (Bill.ofLeaf (((m.terms.map fun t => shapeSize t.w.shape).sum + shapeSize outConst.shape) * fac cExact),
          .mix vtag.terms)
      | .sep _, .wsep _ _ => (Bill.zero, vtag)
      | .sep s, _ =>
        let st := vtag.sepTag
        let pure := st.pure && free ci
        (sepRowsBill ctx s.rows.length (fun p => sepKey self st.origin p) (shapeSize s.rest) pure,
          .sep ⟨pure, st.origin⟩)
      | _, _ => (Bill.zero, .none)
    | .neg _, [.mix m] =>
      (Bill.ofLeaf ((m.terms.map fun t => shapeSize t.w.shape).sum + shapeSize outConst.shape),
        .mix tag0.terms)
    | .sum _ dim, [x] =>
      let st := tag0.sepTag
      let positions := fun (n : Nat) => (List.range n).map fun _ => (⟨st.pure, self, []⟩ : TermTag)
      match x, out with
      | .sep s, .mix _ => (Bill.zero, .mix (positions s.rows.length))
      | .sep s, _ =>
        let nd : Int := (x.shape ctx).length
        let d := if dim ≥ 0 then dim else nd + dim
        let perRow := fun (r : DT) =>
          let size := shapeSize (r.shape.drop 1)
          size - size / r.shape.getD (d.toNat - 1) 1
        (Bill.sum (((List.range s.rows.length).zip s.rows).map fun (p, r) =>
            rowsBill (sepKey self st.origin p) (ctx.range p) (perRow r) st.pure),
          .sep ⟨st.pure, st.origin⟩)
      | .wsep _ s, _ => (Bill.zero, .mix (positions s.rows.length))
      | .wsepv _ s, _ => (Bill.zero, .mix (positions s.rows.length))
      | _, _ => (Bill.zero, .none)
    | .index _ _, [.sep _] => (Bill.zero, .mix [⟨tag0.sepTag.pure, self, []⟩])
    | _, _ => (Bill.zero, .none)

/-! ## One operation, priced -/

/-- `tevalOp` on an operation other than the input, word for word (`tevalOp_eq_args`). -/
def tevalOpArgs (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    (op : Op) : Option TV :=
  match op.args.mapM (vals[·]?) with
  | none => none
  | some args =>
    let plain := fun (vals : Array TV) =>
      ((gevalOp g w (.box ctx.box) (vals.map (·.toGVal ctx)) op).bind GVal.tensor).map TV.dt
    if !(args.any TV.isDomain) then plain vals else
    match tEvaluate ctx (fun b => !deps.getD b true) op args with
    | .val v => some v
    | .fail => none
    | .decline =>
      let left := op.args.mapM fun a => (vals[a]?).bind fun v =>
        if v.isDomain then tLeave ctx v else some v
      match left with
      | none => none
      | some left =>
        let set := fun (vs : List TV) =>
          (op.args.zip vs).foldl (fun acc (a, v) => acc.set! a v) vals
        if left.any TV.isVar then
          match tVarOp ctx op left with
          | .val v => some v
          | .fail => none
          | .decline =>
            match left.mapM fun v => match v with
                | .var vs => (collapseVar vs).map TV.dt
                | v => some v with
            | none => none
            | some boxed => plain (set boxed)
        else plain (set left)

theorem tevalOp_eq_args (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    {op : Op} (hop : op ≠ .input) : tevalOp g w ctx deps vals op = tevalOpArgs g w ctx deps vals op := by
  cases op <;> first | exact absurd rfl hop | rfl

/-- An operation other than the input, priced: `tevalOpArgs`, step by step, with what Python charges on
    each path (`_eval_token`), and the value's tag. -/
def tcostOpArgs (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    (tags : Array Tag) (op : Op) : Option (TV × Tag × Bill) :=
  match op.args.mapM (vals[·]?) with
  | none => none
  | some args =>
    let plain := fun (vals : Array TV) =>
      ((gevalOp g w (.box ctx.box) (vals.map (·.toGVal ctx)) op).bind GVal.tensor).map TV.dt
    let plainBill := fun (v : TV) => match v with
      | .dt out => Bill.ofLeaf (2 * tplainCost g ctx vals out op)
      | _ => Bill.zero
    if !(args.any TV.isDomain) then (plain vals).map fun v => (v, .none, plainBill v) else
    match tEvaluate ctx (fun b => !deps.getD b true) op args with
    | .val v =>
      let bt := ruleBill ctx (fun b => !deps.getD b true) vals.size op args
        (op.args.map fun a => tags.getD a .none) v
      some (v, bt.2, bt.1)
    | .fail => none
    | .decline =>
      -- the arguments leave the domain
      let left := op.args.mapM fun a => (vals[a]?).bind fun v =>
        if v.isDomain then tLeave ctx v else some v
      match left with
      | none => none
      | some left =>
        let set := fun (vs : List TV) =>
          (op.args.zip vs).foldl (fun acc (a, v) => acc.set! a v) vals
        let b0 := Bill.ofLeaf (preDeclineBill ctx op args +
          (args.map fun a => if a.isDomain then leaveBill ctx a else 0).sum)
        if left.any TV.isVar then
          match tVarOp ctx op left with
          | .val v => some (v, .none, b0 + Bill.ofLeaf (varOpBill ctx op left v))
          | .fail => none
          | .decline =>
            match left.mapM fun v => match v with
                | .var vs => (collapseVar vs).map TV.dt
                | v => some v with
            | none => none
            | some boxed => (plain (set boxed)).map fun v =>
                (v, .none, b0 + Bill.ofLeaf (collapseVarsBill op.args left) + plainBill v)
        else (plain (set left)).map fun v => (v, .none, b0 + plainBill v)

theorem tcostOpArgs_fst (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    (tags : Array Tag) (op : Op) :
    (tcostOpArgs g w ctx deps vals tags op).map (·.1) = tevalOpArgs g w ctx deps vals op := by
  unfold tcostOpArgs tevalOpArgs
  generalize op.args.mapM (vals[·]?) = margs
  cases margs with
  | none => rfl
  | some args =>
    dsimp only
    cases hd : (!(args.any TV.isDomain))
    · simp only [Bool.false_eq_true, ite_false]
      generalize tEvaluate ctx (fun b => !deps.getD b true) op args = st
      cases st with
      | val v => rfl
      | fail => rfl
      | decline =>
        dsimp only
        generalize op.args.mapM (fun a => (vals[a]?).bind fun v =>
          if v.isDomain then tLeave ctx v else some v) = mleft
        cases mleft with
        | none => rfl
        | some left =>
          dsimp only
          cases hv : left.any TV.isVar
          · simp only [Bool.false_eq_true, ite_false, Option.map_map]
            rfl
          · simp only [ite_true]
            generalize tVarOp ctx op left = st2
            cases st2 with
            | val v => rfl
            | fail => rfl
            | decline =>
              dsimp only
              generalize left.mapM (fun v => match v with
                | .var vs => (collapseVar vs).map TV.dt
                | v => some v) = mb
              cases mb with
              | none => rfl
              | some boxed =>
                simp only [Option.map_map]
                rfl
    · simp only [ite_true, Option.map_map]
      rfl

/-- One operation of a token_interval leaf with its charge and its tag (`tcostOp_fst`: its value is
    `tevalOp`'s). -/
def tcostOp (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    (tags : Array Tag) (op : Op) : Option (TV × Tag × Bill) :=
  match op with
  | .input =>
    if ctx.box.length == g.positions && ctx.box.all (·.hi < g.values) then some (.box, .none, Bill.zero)
    else none
  | op => tcostOpArgs g w ctx deps vals tags op

theorem tcostOp_fst (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    (tags : Array Tag) (op : Op) :
    (tcostOp g w ctx deps vals tags op).map (·.1) = tevalOp g w ctx deps vals op := by
  by_cases hop : op = .input
  · subst hop
    simp only [tcostOp, tevalOp]
    split <;> rfl
  · rw [tevalOp_eq_args g w ctx deps vals hop, ← tcostOpArgs_fst g w ctx deps vals tags op]
    cases op <;> first | exact absurd rfl hop | rfl

/-- Run the operations in order, with their tags and the bill so far. -/
def tcostOps (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) :
    List Op → Array TV → Array Tag → Bill → Option (Array TV × Array Tag × Bill)
  | [], vals, tags, b => some (vals, tags, b)
  | op :: ops, vals, tags, b =>
    match tcostOp g w ctx deps vals tags op with
    | some (v, t, b') => tcostOps g w ctx deps ops (vals.push v) (tags.push t) (b + b')
    | none => none

theorem tcostOps_fst (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) :
    ∀ (ops : List Op) (vals : Array TV) (tags : Array Tag) (b : Bill),
      (tcostOps g w ctx deps ops vals tags b).map (·.1) = tevalOps g w ctx deps ops vals
  | [], _, _, _ => rfl
  | op :: ops, vals, tags, b => by
    have h := tcostOp_fst g w ctx deps vals tags op
    simp only [tcostOps, tevalOps]
    cases hc : tcostOp g w ctx deps vals tags op with
    | none =>
      rw [hc] at h
      simp only [Option.map_none] at h
      rw [← h]
      rfl
    | some r =>
      obtain ⟨v, t, b'⟩ := r
      rw [hc] at h
      simp only [Option.map_some] at h
      rw [← h]
      exact tcostOps_fst g w ctx deps ops _ _ _

/-! ## The decision, priced (Python's `lower_margin`) -/

/-- A `Mix` output: the constant's margins, each term's weighted differences of rows, the minimum. -/
def mixMarginBill (ctx : TCtx) (m : Mix) : Nat :=
  let n := m.const.shape.getD 1 0
  let rowsN := if ctx.aligned then ctx.k else 1
  (n - 1) + (m.terms.map fun t =>
      let T := t.rows.shape.headD 0
      if ctx.aligned then (if t.w.exact then 3 else 5) * max T (shapeSize t.w.shape) * (n - 1)
      else (3 * T + 8) * (n - 1)).sum + rowsN * (n - 1)

/-- What finding the lowest margin bound of the leaf's output costs. -/
def marginBill (ctx : TCtx) (v : TV) : Nat :=
  match v with
  | .sep _ | .wsep _ _ | .wsepv _ _ =>
    leaveBill ctx v +
      (if ctx.aligned then ctx.k * shapeSize (v.shape ctx) else (v.shape ctx).getD 1 0 - 1)
  | .var vs => vs.size * shapeSize (vs.getD 0 emptyDT).shape
  | .dt x => x.shape.getD 1 0 - 1
  | .mix m => mixMarginBill ctx m
  | .box => 0

/-! ## A leaf, priced -/

/-- A token_interval leaf for the label `l`: its lowest margin bound (as `tokenLeafBound`) and its
    bill. -/
def tokenLeafPriced (g : Graph) (w : DWeights) (box : Box) (l : Nat) :
    Option (Option (Int × Int) × Bill) :=
  let ctx := TCtx.ofBox box g.values
  match tcostOps g w ctx (dependsOnInput g) g.nodes #[] #[] Bill.zero with
  | none => none
  | some (vals, _, bill) =>
    match vals[g.output]? with
    | none => none
    | some out =>
      match out.shape ctx with
      | [1, n] =>
        if l < n then (lowestMargin ctx out l).map fun r => (r, bill + Bill.ofLeaf (marginBill ctx out))
        else none
      | _ => none

theorem tokenLeafPriced_bound {g : Graph} {w : DWeights} {box : Box} {l : Nat}
    {r : Option (Int × Int)} {b : Bill} (h : tokenLeafPriced g w box l = some (r, b)) :
    tokenLeafBound g w box l = some r := by
  unfold tokenLeafPriced at h
  unfold tokenLeafBound
  dsimp only at h ⊢
  cases hc : tcostOps g w (TCtx.ofBox box g.values) (dependsOnInput g) g.nodes #[] #[] Bill.zero with
  | none => rw [hc] at h; cases h
  | some p =>
    obtain ⟨vals, tags, bill⟩ := p
    have hv : tevalOps g w (TCtx.ofBox box g.values) (dependsOnInput g) g.nodes #[] = some vals := by
      rw [← tcostOps_fst g w (TCtx.ofBox box g.values) (dependsOnInput g) g.nodes #[] #[] Bill.zero, hc]
      rfl
    rw [hc] at h
    simp only [hv, Option.bind_eq_bind, Option.bind_some]
    cases ho : vals[g.output]? with
    | none => simp only [ho] at h; cases h
    | some out =>
      simp only [ho] at h
      simp only [Option.bind_some]
      generalize TV.shape (TCtx.ofBox box g.values) out = s at h ⊢
      match s, h with
      | [1, n], h =>
        by_cases hl : l < n
        · simp only [hl, ite_true] at h ⊢
          obtain ⟨r', hr', he⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at he
          rw [hr', he.1]
        · simp only [hl, ite_false] at h
          cases h

/-- A token_interval leaf of a proof: `false` and no charge if the box has no constant label (Python
    never runs the rule there); else the verdict, the leaf's charge to `token_interval` and its
    requests for pure rows. `none` where Python rejects the proof. -/
def gtokenLeaf (g : Graph) (w : DWeights) (task : Task) (box : Box) : Option (Bool × Nat × List RowReq) :=
  match task.constantLabel box with
  | none => some (false, 0, [])
  | some l =>
    match tokenLeafPriced g w box l with
    | some (r, b) =>
      some ((match r with
        | none => true
        | some (m, _) => decide (0 < m)), b.leaf, b.reqs)
    | none => none

theorem gtokenLeaf_verdict {g : Graph} {w : DWeights} {task : Task} {box : Box} {v : Bool} {k : Nat}
    {rq : List RowReq} (h : gtokenLeaf g w task box = some (v, k, rq)) :
    generalTokenInterval g w task box = some v := by
  unfold gtokenLeaf at h
  unfold generalTokenInterval
  cases hl : task.constantLabel box with
  | none =>
    simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
    simp only [h.1]
  | some l =>
    simp only [hl] at h
    cases hp : tokenLeafPriced g w box l with
    | none => simp [hp] at h
    | some p =>
      obtain ⟨r, b⟩ := p
      simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
      dsimp only
      rw [tokenLeafPriced_bound hp, Option.map_some, ← h.1]
      cases r <;> rfl

/-! ## The tables: pure rows once per proof -/

/-- The tokens `lo..hi` not in the mask. -/
def missingTokens (mask lo hi : Nat) : Nat :=
  (List.range (hi + 1 - lo)).foldl (fun n j => if mask.testBit (lo + j) then n else n + 1) 0

/-- The mask of the tokens `lo..hi`. -/
def rangeMask (lo hi : Nat) : Nat := (1 <<< (hi + 1)) - (1 <<< lo)

/-- The tokens whose rows are kept, per memo key. -/
abbrev Memo := List (List Nat × Nat)

def Memo.get (memo : Memo) (key : List Nat) : Nat :=
  match memo.find? (·.1 == key) with
  | some (_, m) => m
  | none => 0

def Memo.put (memo : Memo) (key : List Nat) (mask : Nat) : Memo :=
  if memo.any (·.1 == key) then memo.map fun (k, m) => if k == key then (k, mask) else (k, m)
  else (key, mask) :: memo

/-- One request: the rows not kept yet are computed, charged and kept. -/
def tablesStep (acc : Memo × Nat) (r : RowReq) : Memo × Nat :=
  let mask := acc.1.get r.key
  (acc.1.put r.key (mask ||| rangeMask r.lo r.hi), acc.2 + r.cost * missingTokens mask r.lo r.hi)

/-- The charge to `tables` of a proof's requests, in order. -/
def tablesCharge (reqs : List RowReq) : Nat := (reqs.foldl tablesStep ([], 0)).2

/-! ## A proof's token_interval leaves -/

/-- The token_interval rule on a list of leaves: the verdicts, the charge to `token_interval` and the
    charge to `tables`, the pure rows shared by the leaves as Python shares them over a proof. -/
def gtokenRun (g : Graph) (w : DWeights) (task : Task) (boxes : List Box) :
    Option (List Bool × Nat × Nat) :=
  match boxes.mapM (gtokenLeaf g w task) with
  | none => none
  | some rs => some (rs.map (·.1), (rs.map (·.2.1)).sum, tablesCharge (rs.flatMap (·.2.2)))

/-! ## The counted operation (the maximum-knowledge condition) -/

namespace CostM

/-- The token_interval rule on a general network, for the leaves `boxes` of one proof: the verdict of each
    (`false`, not an error, for a box without a constant label), charged as cost-v3 charges them, the
    leaves' own work to `token_interval` and the rows that depend on their token alone to `tables`, each
    row once over the list, as Python keeps them over a proof. A checker that calls this several times
    pays for those rows in each call: one call with all its leaves pays Python's price exactly. `none` if
    the weights are not dyadic or the rule cannot follow the network on one of the leaves. -/
def gtokenIntervals (g : Graph) (task : Task) (boxes : List Box) : CostM (List Bool) := ⟨fun env c =>
  match dweights env.weights with
  | none => none
  | some dw =>
    match gtokenRun g dw task boxes with
    | some (bs, k, t) => some (bs, (c.add "token_interval" k).add "tables" t)
    | none => none⟩

theorem gtokenIntervals_run_of {g : Graph} {task : Task} {boxes : List Box} {env : Env} {c : Cost}
    {bs : List Bool} {k t : Nat}
    (h : ((dweights env.weights).bind fun dw => gtokenRun g dw task boxes) = some (bs, k, t)) :
    (gtokenIntervals g task boxes).run env c = some (bs, (c.add "token_interval" k).add "tables" t) := by
  show (match dweights env.weights with
    | none => none
    | some dw =>
      match gtokenRun g dw task boxes with
      | some (bs, k, t) => some (bs, (c.add "token_interval" k).add "tables" t)
      | none => none) = _
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h
  | some dw =>
    simp only [hdw, Option.bind_some] at h
    simp only [h]

end CostM

/-- One fact per leaf, for an instance proof that decides each leaf in a theorem of its own (the kernel's
    memory grows with every leaf it evaluates within one theorem): leaf `i` of `boxes` gives `rs[i]`. -/
def TokenLeafFacts (env : Env) (g : Graph) (task : Task) :
    List Box → List (Bool × Nat × List RowReq) → Prop
  | [], [] => True
  | b :: bs, r :: rs =>
    ((dweights env.weights).bind fun dw => gtokenLeaf g dw task b) = some r ∧ TokenLeafFacts env g task bs rs
  | _, _ => False

theorem mapM_gtokenLeaf_of_facts {env : Env} {g : Graph} {task : Task} {dw : DWeights}
    (hdw : dweights env.weights = some dw) :
    ∀ {boxes : List Box} {rs : List (Bool × Nat × List RowReq)},
      TokenLeafFacts env g task boxes rs → boxes.mapM (gtokenLeaf g dw task) = some rs
  | [], [], _ => rfl
  | b :: bs, r :: rs, h => by
    obtain ⟨hb, hbs⟩ := h
    rw [hdw, Option.bind_some] at hb
    simp only [List.mapM_cons, hb, mapM_gtokenLeaf_of_facts hdw hbs]
    rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- How an instance with a token_interval call splits: from one decided fact per leaf, the run of the call,
    with the charges added up (`tablesCharge` of the leaves' requests, a computation on the facts' small
    lists of requests). Stated for the list as the checker names it, so that the kernel compares identical
    terms: had it to match the checker's list against a list written out, it would unfold the call's run
    first, and that runs every leaf at once. -/
theorem CostM.gtokenIntervals_run_of_facts {g : Graph} {task : Task} {env : Env} {c : Cost}
    {boxes : List Box} {rs : List (Bool × Nat × List RowReq)} (hne : boxes ≠ [])
    (h : TokenLeafFacts env g task boxes rs) :
    (gtokenIntervals g task boxes).run env c =
      some (rs.map (·.1), (c.add "token_interval" (rs.map (·.2.1)).sum).add "tables"
        (tablesCharge (rs.flatMap (·.2.2)))) := by
  cases hdw : dweights env.weights with
  | none =>
    cases boxes with
    | nil => exact absurd rfl hne
    | cons b bs =>
      cases rs with
      | nil => exact h.elim
      | cons r rs =>
        have h1 := h.1
        rw [hdw] at h1
        cases h1
  | some dw =>
    apply gtokenIntervals_run_of
    rw [hdw, Option.bind_some]
    unfold gtokenRun
    rw [mapM_gtokenLeaf_of_facts hdw h]

end CompactCheck

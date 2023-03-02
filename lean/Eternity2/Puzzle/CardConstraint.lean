import LeanSAT
import Eternity2.AuxDefs

namespace Eternity2.Encoding

open LeanSAT Encode

structure CardConstraint where
  lits : Std.RBMap Var Int (compare (α := Nat))
  weight : Int
deriving Inhabited

namespace CardConstraint

instance : ToString CardConstraint where
  toString | ⟨lits, leWeight⟩ => s!"∑ {lits.toList} = {leWeight}"

def add : CardConstraint → CardConstraint → CardConstraint
| ⟨lits1, w1⟩, ⟨lits2, w2⟩ =>
  ⟨ Std.RBMap.mergeWith (fun _ => (· + ·)) lits1 lits2
    |>.filter (fun _ i => i ≠ 0)
  , w1 + w2⟩

instance : Add CardConstraint := ⟨add⟩

def scale (factor : Int) : CardConstraint → CardConstraint
| {lits, weight} => 
  ⟨ lits.mapVal (fun _ => (· * factor))
  , weight * factor ⟩

instance : HMul Int CardConstraint CardConstraint := ⟨scale⟩

def neg : CardConstraint → CardConstraint := scale (-1)

instance : Neg CardConstraint := ⟨neg⟩

def sub := (· + neg ·)
instance : Sub CardConstraint := ⟨sub⟩

def reduceCoeffs : CardConstraint → CardConstraint
| {lits,weight} =>
  let gcd := (lits.foldl (fun gcd _ w => gcd.gcd w) weight)
  let gcd := if weight < 0 then -gcd else gcd
  {lits := lits.mapVal (fun _ => (· / gcd)), weight := weight / gcd}

def encode (cc : CardConstraint) : EncCNF Unit :=
  let cc := if cc.weight < 0 then cc.neg else cc
  let lits := cc.lits.foldl (fun acc v i =>
    match compare i 0 with
    | .eq => acc
    | .gt =>
      Function.iterate (Array.push · (.pos v)) i.natAbs acc
    | .lt =>
      Function.iterate (Array.push · (.neg v)) i.natAbs acc
    ) #[]
  equalK lits cc.weight.natAbs

def ofLits (l : List Literal) (weight : Int) : CardConstraint :=
  l.foldl (fun
      | ⟨map, weight⟩, .pos v =>
        ⟨map.alter v (fun | .none => some 1 | .some w => some (w+1)), weight⟩
      | ⟨map, weight⟩, .neg v =>
        ⟨map.alter v (fun | .none => some (-1) | .some w => some (w-1)), weight-1⟩
      )
    ⟨.empty, weight⟩


end CardConstraint

structure EncCard.State where
  clauses : List CardConstraint

@[reducible]
def EncCard := StateM EncCard.State

namespace EncCard

instance : ToString State where
  toString | ⟨clauses⟩ => String.intercalate "\n" (clauses.map toString)

instance [Inhabited α] : Inhabited (EncCard α) := ⟨do return default⟩

nonrec def run (s : State) (e : EncCard α) : α × State := e.run s

def State.new : State := ⟨[]⟩
def State.unsat : State := ⟨[⟨.ofList [] _, 1⟩]⟩

nonrec def new : EncCard α → α × State := run .new


instance : MonadLift EncCard EncCNF where
  monadLift c := do
    let (a,state) := c (.mk [])
    for c in state.clauses do
      c.encode
    return a

def addClause (cc : CardConstraint) : EncCard Unit := do
  StateT.set (.mk (cc::(← get).clauses))

def gaussElim : EncCard Unit := do
  StateT.set <| aux (←get).clauses []
where
  aux (cs : List CardConstraint) (acc : List CardConstraint) :=
    match cs with
    | [] => ⟨acc⟩
    | c::cs =>
      match c.lits.min with
      | none => if c.weight = 0 then aux cs acc else .unsat
      | some (pvar, _) =>
      let cs' := cs.map (pivot pvar c)
      let acc' := acc.map (pivot pvar c)
      aux cs' (c::acc')
  pivot (pvar : Var) (piv other : CardConstraint) :=
    match piv.lits.find? pvar, other.lits.find? pvar with
    | none, _ => panic! "pivot does not have pvar"
    | _, none => other
    | some pw, some ow =>
      if pw = 0 || ow = 0 then panic! "zero coeff" else
      let piv := if pw < 0 then -piv else piv
      let pw := pw.natAbs
      let other := if ow < 0 then -other else other
      let ow := ow.natAbs
      let lcm := Nat.lcm pw ow
      let newClause := (lcm / ow : Int) * other - (lcm / pw : Int) * piv
      newClause.reduceCoeffs
termination_by aux cs _ => cs.length

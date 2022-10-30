import Std
import Eternity2.AuxDefs

open Std

namespace EncCNF

def Var := Nat
deriving Inhabited, DecidableEq, Hashable, Repr

/-- Either `v` or `¬v` for variable `v`. -/
structure Literal where
  var : Var
  neg : Bool
deriving Inhabited, DecidableEq, Hashable, Repr

def Clause := List Literal
deriving Inhabited, DecidableEq, Hashable, Repr

/-- State for an encoding -/
structure State where
  numVars : Nat
  clauses : List Clause
  names : HashMap Nat String
  varCtx : String

namespace State

def printAux (println : String → IO Unit)
  : State → IO Unit
| ⟨numVars, clauses, names, _⟩ => do
  println s!"p cnf {numVars} {clauses.length}"
  for i in [0:numVars] do
    println s!"c {i+1} {names.find? i |>.get!}"
  for c in clauses do
    let nums := c.map (fun ⟨v, neg⟩ =>
      if neg then "-" ++ toString v.succ else toString v.succ
    )
    println (String.intercalate " " (nums ++ ["0"]))

def printDIMACS := printAux IO.println

def checkSAT (cnfFile : String) (s : State) 
  : IO (Option (HashMap String Bool)) := do
  -- Write formula to cnfFile
  IO.FS.withFile cnfFile .write (fun handle =>
    printAux handle.putStrLn s
  )
  -- Run cadical on cnfFile
  let out := (← IO.Process.output {
    stdin := .piped
    stdout := .piped
    stderr := .piped
    cmd := "cadical"
    args := #[cnfFile]
  }).stdout
  let lines := out.splitOn "\n" |>.filter (not <| ·.startsWith "c")
  match lines with
  | "s SATISFIABLE" :: satis =>
    return some (
      satis
      |>.filter (not <| ·.isEmpty)
      |>.map (·.drop 2 |>.splitOn " ")
      |>.join
      |>.map (·.toInt!)
      |>.filter (· ≠ 0)
      |>.foldl (fun acc i =>
          acc.insert (s.names.find? (Int.natAbs i) |>.get!) (i > 0)
        ) (HashMap.empty)
    )
  | "s UNSATISFIABLE" :: _ => return none
  | _ =>
    IO.println out
    return none

end State

end EncCNF

@[reducible]
def EncCNF := StateM EncCNF.State

namespace EncCNF

nonrec def run (e : EncCNF α) : α × EncCNF.State :=
  e.run ⟨0, [], HashMap.empty, ""⟩

def newCtx (name : String) (inner : EncCNF α) : EncCNF α := do
  let oldState ← get
  set {oldState with varCtx := oldState.varCtx ++ name}
  let res ← inner
  let newState ← get
  set {newState with varCtx := oldState.varCtx}
  return res

def mkVar (name : String) : EncCNF Var := do
  let oldState ← get
  set { oldState with
    numVars := oldState.numVars+1,
    names := oldState.names.insert oldState.numVars
                (oldState.varCtx ++ name)}
  return oldState.numVars

def addClause (C : Clause) : EncCNF Unit := do
  let oldState ← get
  set { oldState with
    clauses := C :: oldState.clauses }

def mkTemp : EncCNF Var := do
  let oldState ← get
  return ← mkVar ("tmp" ++ toString oldState.numVars)


example : IO Unit := do
  let ((), enc) := run do
    let x ← mkVar "x1"
    newCtx "hi." do
      let t1 ← mkTemp
      addClause [⟨t1, true⟩, ⟨x,false⟩]
    let t ← mkTemp
    addClause [⟨t,true⟩, ⟨x, true⟩]
  enc.printDIMACS


structure VarBlock (dims : List Nat) where
  start : Var
  h_dims : dims.length > 0

@[reducible, inline]
def VarBlock.hdLen : VarBlock ds → Nat
| ⟨_, _⟩ =>
  match ds with
  | [] => by contradiction
  | d::_ => d

@[reducible, inline]
def VarBlock.elemTy : List Nat → Type
  | [] => Empty
  | [_] => Var
  | _::d'::ds' => VarBlock (d'::ds')

@[inline]
def VarBlock.get (v : VarBlock ds) (i : Fin v.hdLen)
  : VarBlock.elemTy ds
  := match ds, v with
  | [],         ⟨_    ,_⟩ => by contradiction
  | [_],        ⟨start,_⟩ => Nat.add start i
  | _::d'::ds', ⟨start,_⟩ =>
    ⟨Nat.add start (Nat.mul i ((d'::ds').foldl (· * ·) 1)), by
      simp; apply Nat.zero_lt_succ⟩ 

instance : GetElem (VarBlock ds) Nat (VarBlock.elemTy ds) (fun v i => i < v.hdLen) where
  getElem v i h := v.get ⟨i,h⟩


def mkVarBlock (name : String) (dims : List Nat) (h : dims.length > 0 := by simp)
  : EncCNF (VarBlock dims) := do
  let state ← get
  let start := state.numVars
  gen dims name
  return ⟨start, h⟩
where gen (dims : List Nat) (pref : String) : EncCNF Unit := do
  match dims with
  | [] =>
    let _ ← mkVar pref
  | d::ds =>
    for i in [0:d] do
      gen ds s!"{pref}[{i}]"

def mkTempBlock (dims : List Nat) (h : dims.length > 0 := by simp)
  : EncCNF (VarBlock dims) := do
  return ← mkVarBlock ("tmp" ++ toString (← get).numVars) dims h

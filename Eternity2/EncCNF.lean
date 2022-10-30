import Std
import Eternity2.AuxDefs

open Std

namespace EncCNF

def Var := Nat
deriving Inhabited, DecidableEq, Hashable, Repr, ToString

/-- Either `v` or `¬v` for variable `v`. -/
structure Literal where
  var : Var
  neg : Bool
deriving Inhabited, DecidableEq, Hashable, Repr

instance : ToString Literal where
  toString | ⟨v,n⟩ => s!"{if n then "¬" else ""}{v}"

nonrec def Literal.not : Literal → Literal
| ⟨v,n⟩ => ⟨v, not n⟩

def Clause := List Literal
deriving Inhabited, DecidableEq, Hashable, Repr, ToString

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

def printFileDIMACS (cnfFile : String) (s : State) : IO Unit := do
  -- Write formula to cnfFile
  IO.FS.withFile cnfFile .write (fun handle =>
    printAux handle.putStrLn s
  )

def appendFileDIMACSClause (cnfFile : String) (c : Clause) (_ : State) : IO Unit := do
    let nums := c.map (fun ⟨v, neg⟩ =>
        if neg then "-" ++ toString v.succ else toString v.succ
      )
    IO.FS.withFile cnfFile .append (fun handle =>
      handle.putStrLn (String.intercalate " " (nums ++ ["0"]))
    )

end State

end EncCNF

@[reducible]
def EncCNF := StateM EncCNF.State

namespace EncCNF

nonrec def run (s : State) (e : EncCNF α) : α × State := e.run s

nonrec def new : EncCNF α → α × State := run ⟨0, [], HashMap.empty, ""⟩

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
  let ((), enc) := new do
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

@[reducible, inline, simp]
def VarBlock.hdLen : VarBlock ds → Nat
| ⟨_, _⟩ =>
  match ds with
  | [] => by contradiction
  | d::_ => d

@[reducible, inline, simp]
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

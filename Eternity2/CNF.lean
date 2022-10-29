import Std

open Std

-- **************************
-- *   Generic CNF stuff    *
-- **************************

@[reducible]
def Atom := String
deriving Inhabited, DecidableEq, Hashable, Repr

structure Literal where
  neg : Bool
  atom : Atom
deriving Inhabited, DecidableEq, Hashable, Repr

namespace Literal

nonrec def not : Literal → Literal
| ⟨neg,name⟩ => ⟨not neg, name⟩

instance : ToString Literal where
  toString := λ ⟨neg, num⟩ =>
    if neg then "¬" ++ num else num

end Literal

structure Clause where
  lits : List Literal
  original : List Literal := lits -- represents "original" clause before simplifications
deriving Inhabited, DecidableEq, Repr

instance : ToString Clause where
  toString := λ L => "(" ++ String.intercalate " ∨ " (L.lits.map Literal.instToStringLiteral.toString) ++ ")"

structure Formula where
  clauses : List Clause
deriving Inhabited

instance : ToString Formula where
  toString := λ L => String.intercalate " ∧ " (L.clauses.map instToStringClause.toString)

def Formula.buildAtomMap : Formula → Nat × HashMap Atom Nat × HashMap Nat Atom
| ⟨clauses⟩ =>
  let (nameMap, lastVar, _) := clauses.foldl
    (fun acc c =>
      c.lits.foldl (fun (map,last,count) ⟨_,atom⟩ =>
        -- if `atom` is in map, do nothing, else assign `atom` to next
        match map.find? atom with
        | some _  => (map,last,count+1)
        | none    => (map.insert atom (last+1), last+1,count+1)
      )
    acc
  ) (HashMap.empty, 0, 0)
  let revMap := nameMap.fold (fun acc k v => acc.insert v k) (HashMap.empty)
  (lastVar, nameMap, revMap)

def Formula.printFromMap (println : String → IO Unit)
  : Formula → Nat × HashMap Atom Nat × HashMap Nat Atom → IO Unit
| ⟨clauses⟩, ⟨lastVar, nameMap, revMap⟩ => do
  println s!"p cnf {lastVar} {clauses.length}"
  for i in [1:lastVar+1] do
    println s!"c {i} {revMap.find? i |>.get!}"
  for c in clauses do
    let nums := c.lits.map (fun ⟨neg,a⟩ =>
      let n := nameMap.find? a |>.get!
      if neg then "-" ++ toString n else toString n
    )
    println (String.intercalate " " (nums ++ ["0"]))

def Formula.printDimacs (f : Formula) : IO Unit :=
  f.printFromMap (IO.println) (f.buildAtomMap)

def Formula.checkSAT (f : Formula) (cnfFile : String) 
  : IO (Option (HashMap String Bool)) := do
  let mapStuff := f.buildAtomMap
  -- Write formula to cnfFile
  IO.FS.withFile cnfFile .write (fun handle =>
    f.printFromMap handle.putStrLn mapStuff
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
          acc.insert (mapStuff.2.2.find? (Int.natAbs i) |>.get!) (i > 0)
        ) (HashMap.empty)
    )
  | "s UNSATISFIABLE" :: _ => return none
  | _ =>
    IO.println out
    return none
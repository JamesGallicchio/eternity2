import Eternity2.SATSolve

namespace Numberlink

structure NumberLinkProblem where
  width : Nat
  height : Nat
  nums : Nat
  poses : List (Fin nums × Fin height × Fin width)
deriving Inhabited

structure NumberLinkVars where
  problem : NumberLinkProblem
  piece_var : Fin problem.height → Fin problem.width → Fin problem.nums → EncCNF.Var
deriving Inhabited

def numberLink (prob : NumberLinkProblem) : EncCNF NumberLinkVars :=
  open EncCNF in do
  /- make variables -/
  let arr ← Array.initM prob.height fun i =>
    Array.initM prob.width fun j =>
      Array.initM prob.nums fun n =>
        mkVar s!"pos {i} {j} numbered {n}"

  /- helper function to get the i,j,n variable -/
  let piece_var : Fin prob.height → Fin prob.width → Fin prob.nums → Var := fun i j n =>
    arr[i]![j]![n]!

  /- helper function to get the neighbors of i j -/
  let neighbors (i j) : List (_ × _):= [
      i.pred?.map (⟨·, j⟩) |>.toList,
      i.succ?.map (⟨·, j⟩) |>.toList,
      j.pred?.map (⟨i, ·⟩) |>.toList,
      j.succ?.map (⟨i, ·⟩) |>.toList
    ].join

  for i in List.fins _ do
    for j in List.fins _ do
      /- check if the square is in the given positions -/
      match prob.poses.find? (fun elem => (i,j) = elem.2) with
      | none =>
        /- assign at most one color to square i,j -/
        EncCNF.atMostOne (List.fins _ |>.map fun n => piece_var i j n)
        /- if a color assigned to this square, exactly two neighbors
          must share that color -/
        for n in List.fins _ do
          EncCNF.condEqualK
            [piece_var i j n]
            (neighbors i j |>.map fun (i',j') => piece_var i' j' n).toArray
            2
      | some (n, _, _) =>
        /- assign the square to n -/
        for n' in List.fins _ do
          if n = n' then
            EncCNF.addClause [piece_var i j n]
          else
            EncCNF.addClause [.not <| piece_var i j n']
        /- exactly one neighbor must share this color -/
        EncCNF.equalK (neighbors i j |>.map fun (i',j') => piece_var i' j' n).toArray 1

  return ⟨prob, piece_var⟩

def main' : IO Unit := do
  let prob : NumberLinkProblem := {
    width := 9
    height := 8
    nums := 8
    poses := [
      (1, 3, 3),
      (1, 4, 6),
      (2, 7, 0),
      (2, 2, 1),
      (3, 3, 1),
      (3, 4, 4),
      (4, 4, 3),
      (4, 3, 8),
      (5, 6, 2),
      (5, 6, 7),
      (6, 1, 4),
      (6, 1, 7),
      (7, 2, 4),
      (7, 3, 6),
      (8, 1, 1),
      (8, 2, 3)
    ]
  }
  let (vars, enc) := EncCNF.new! <| numberLink prob
--  enc.prettyPrintAux (IO.println)
  match SATSolve.solve enc (
    List.fins _ |>.bind fun i =>
    List.fins _ |>.bind fun j =>
    List.fins _ |>.map fun c =>
    vars.piece_var i j c
  ) with
  | (_, .error) => IO.println "err"
  | (_, .unsat) => IO.println "unsat"
  | (_, .sat assn) =>
    for i in List.fins _ do
      for j in List.fins _ do
--        for n in List.fins _ do
--          if assn.find? (vars.piece_var i j n) = some true then
--            IO.println s!"{i},{j} is {n}"
        match (List.fins _).find? (fun n =>
          assn.find? (vars.piece_var i j n) |>.get!)
        with
        | none =>
          IO.print " "
        | some n =>
          IO.print n
      IO.println ""

#eval main'

end Numberlink

namespace Akari

inductive AkariSquare
| space | filled (num : Option (Fin 5))
deriving DecidableEq, Inhabited

structure AkariProblem where
  height : Nat
  width : Nat
  board : Fin height → Fin width → AkariSquare
deriving Inhabited

def AkariProblem.ofString (s : String) : Except String AkariProblem := do
  let lines := s.split (· = '\n') |>.toArray
  let height := lines.size
  if h_h : height = 0 then
    throw "board must have at least one line?"
  else
    let width := lines[0]'(Nat.pos_of_ne_zero h_h) |>.length
    let arr : Array (Σ' A : Array AkariSquare, A.size = width)
      ← lines.mapIdxM (fun i line => do
        if h_w : width = line.length then
          let A ← Array.initM width (fun j => do
            match line[h_w ▸ j] with
            | ' ' => return .space
            | 'X' => return .filled none
            | '0' => return .filled (some 0)
            | '1' => return .filled (some 1)
            | '2' => return .filled (some 2)
            | '3' => return .filled (some 3)
            | '4' => return .filled (some 4)
            | _ => throw s!"line {i} col {j} unknown character: `{line[h_w ▸ j]}`")
          have : A.size = width := sorry
          return ⟨A, this⟩
        else throw s!"line {i} has width {line.length}; expected {width}"
      )
    have : arr.size = height := sorry
    return ⟨height, width, fun i j => let ⟨A,h⟩ := arr.get (this ▸ i); A.get (h ▸ j)⟩

structure AkariVars extends AkariProblem where
  isLight : Fin height → Fin width → EncCNF.Var
deriving Inhabited

def encode : AkariProblem → EncCNF AkariVars
| ⟨height, width, board⟩ => do
  let varArr ←
    Array.initM height fun r =>
      Array.initM width fun c =>
        EncCNF.mkVar s!"{r},{c} lit"
  let isLight (i : Fin height) (j : Fin width) := varArr[i]![j]!
  
  /- For each row/column, at most one of each contiguous line
    of `space`s can be a light -/
  for r in List.fins height do
    for cs in List.fins width |>.splitOnP (board r · ≠ .space) do
      EncCNF.atMostOne (cs.map (isLight r ·))
  for c in List.fins width do
    for rs in List.fins height |>.splitOnP (board · c ≠ .space) do
      EncCNF.atMostOne (rs.map (isLight · c))
  
  for r in List.fins height do
    for c in List.fins width do
      match board r c with
      | .space =>
        /- Each space square must have a light somewhere in the
          vertical/horizontal sections it is in -/
        /- find rows "adjacent" to r,c -/
        let rs := List.fins height  |>.splitOnP (board · c ≠ .space)
                                    |>.find? (·.contains r) |>.getD []
        /- sim for columns -/
        let cs := List.fins width  |>.splitOnP (board r · ≠ .space)
                                    |>.find? (·.contains c) |>.getD []
        /- at least one of these spaces must be light (note the list
          contains `isLight r c` twice, but that is fine) -/
        EncCNF.addClause (
          rs.map (β := EncCNF.Literal) (isLight · c) ++
            cs.map (β := EncCNF.Literal) (isLight r ·)
        )
      | .filled num =>
        /- filled is not light -/
        EncCNF.addClause [.not (isLight r c)]
        /- if `num = some k` then `k` of `r,c`'s neighbors should
          be light -/
        match num with
        | none => pure ()
        | some k =>
          let nbrs :=  [
              r.pred?.map (isLight · c),
              r.succ?.map (isLight · c),
              c.pred?.map (isLight r ·),
              c.succ?.map (isLight r ·)
            ].map (·.toList.map .ofVar) |>.join
          EncCNF.equalK nbrs.toArray k

  return ⟨⟨height, width, board⟩, isLight⟩

def solve (p : AkariProblem) :=
  let (v,enc) := EncCNF.new! (encode p)
  let varList :=
    List.fins _ |>.bind fun i =>
      List.fins _ |>.map fun j =>
        v.isLight i j
  match SATSolve.solve enc varList with
  | (_, .error) => IO.println "error"
  | (_, .unsat) => IO.println "unsat"
  | (_, .sat assn) =>
    for i in List.fins _ do
      for j in List.fins _ do
        match assn.find? (v.isLight i j) with
        | none => panic! "wtf"
        | some true => IO.print "O"
        | some false =>
          match v.board i j with
          | .space => IO.print " "
          | .filled none => IO.print "X"
          | .filled (some n) => IO.print s!"{n}"
      IO.println ""

#eval match AkariProblem.ofString
"    X    
  0    1 
    X    
1 X   X  
    0    
  X   1  
1   X   X
         
  1 X 1  " with
| .error s => IO.println s
| .ok a => solve a

end Akari
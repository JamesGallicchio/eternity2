import Eternity2

open Eternity2
open System

def genTileSet (size coreColors edgeColors : Nat) : IO TileSet := do
  let b ← DiamondBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b false
  return t.tileSet coreColors

def fetchEternity2Tiles : IO TileSet :=
  TileSet.fromFile "puzzles/e2pieces.txt"

def signSols (ts : TileSet) (reportProgress : Bool := false) : IO (List TileSet) := do
  let (tsVars, enc) := EncCNF.new (do
    let tsVars ← Constraints.colorCardConstraints ts.tiles 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)

  -- Need a plain list of variables to check each time we solve
  let tsVars' := tsVars.map (·.2)

  return (← SATSolve.allSols enc tsVars' reportProgress)
    |>.map fun sol =>
      ⟨ tsVars.map (fun (t,v) =>
            {t with sign := sol.find? v |>.map (fun | true => .plus | false => .minus)})
      , ts.size
      , ts.colors⟩

section variable (size : Nat) (iters := 100) (reportProgress := true)

def sampleSolutionCounts := do
  let mut counts := []
  let width := 80
  IO.print ("[".pushn ' ' width ++ "]")
  for i in [0:iters] do
    if reportProgress then
      let stars := (width * i + width / 2 + 1) / iters
      IO.print ("\r[".pushn '*' stars |>.pushn ' ' (width-stars) |>.push ']')
      (←IO.getStdout).flush
    let ts ← genTileSet size (size + 1) (Nat.sqrt size + 1)
    let sols ← signSols ts
    counts := sols.length :: counts

  IO.println ""
  return counts

def printSolutionCountStats := do
  let counts ← sampleSolutionCounts size
  IO.println s!"counts: {counts}"
  let avg := (counts.foldl (· + ·) (counts.length / 2)) / counts.length
  let var := (counts.foldl (fun acc x => acc + (x - avg) * (x - avg)) (counts.length / 2)) / counts.length
  IO.println s!"avg: {avg}"
  IO.println s!"var: {var}"
  IO.println s!"std: {Nat.sqrt var}"
end

def plotData (size : Nat) : IO Unit := do
  IO.FS.createDirAll "plots"
  let plotsDir : FilePath := "./plots"
  let outputFile : FilePath := plotsDir / "output.csv"
  IO.FS.createDirAll (plotsDir / "board")
  let boardsDir : FilePath := plotsDir / "board"
  let mut i := 0
  let mut j := 0
  IO.FS.withFile outputFile .write (fun handle =>
    handle.putStrLn ("title,size,colors,kind,solutions")
  )
  while i < 9 do
    let colors := size + i - 1
    j := 0
    while j < 10 do
      let tiles ← genTileSet size colors 3
      let boardTitle := s!"{size}_{colors}_{j}"

      IO.println s!"Board: {boardTitle}"

      TileSet.toFile
        (boardsDir / s!"board_{boardTitle}.txt").toString
        tiles
      let (tvs, state) := EncCNF.new do
        Constraints.colorCardConstraints tiles.tiles colors
      let sols ← SATSolve.allSols state (reportProgress := true) (List.map (·.2) tvs)

      IO.FS.withFile outputFile .append (fun handle =>
        handle.putStrLn (s!"{boardTitle},{size},{colors},sign,{sols.length}")
      )
      j := j + 1
    i := i + 1

def main : IO Unit := do
  plotData 6
  -- let ts ← genTileSet 2 3 3
  -- IO.println ts
  -- match EncCNF.new do
  --   Constraints.puzzleConstraints ts
  -- with
  -- | (.error s, _) => IO.println s!"failed to generate encoding: {s}"
  -- | (.ok tsv, enc) =>
  -- let pVars :=
  --   List.fins _ |>.bind fun p =>
  --   List.fins _ |>.bind fun r =>
  --   List.fins _ |>.map fun c =>
  --   tsv.piece_vars p ⟨r,c⟩
  -- let dVars :=
  --   Constraints.DiamondIndex.all _ |>.bind fun d =>
  --   List.fins _ |>.map fun i =>
  --   tsv.diamond_vars d i
  -- EncCNF.State.printFileDIMACS "test.cnf" enc
  -- EncCNF.State.prettyPrintAux IO.println enc
  -- let mut run := true
  -- let mut sol := SATSolve.solve enc pVars
  -- while run do
  --   match sol with
  --   | none =>
  --       run := false
  --       IO.println "unsat"
  --   | some (solver, assn) =>
  --   let board : TileBoard 3 := {
  --     board := Array.init _ fun r =>
  --       Array.init _ fun c =>
  --         List.fins _
  --         |>.find? (fun p => assn.findD (tsv.piece_vars p ⟨r,c⟩) false)
  --         |> (fun
  --           | none => ⟨none, none, none, none, none⟩
  --           | some p => ts.tiles[p]!)
  --     board_size := sorry
  --     isFinalized := true
  --     finalize := sorry
  --   }
  --   IO.println board
  --   IO.println ""
  --   let newClause : EncCNF.Clause :=
  --     pVars.filterMap (fun v => assn.find? v |>.map (⟨v, ·⟩))
  --   sol := SATSolve.addAndResolve solver newClause pVars

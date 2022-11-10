import Eternity2

open Eternity2
open System

def genTileSet (size coreColors edgeColors : Nat) : IO (TileSet size coreColors) := do
  let b ← DiamondBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b false
  return t.tileSet coreColors

def fetchEternity2Tiles : IO (TileSet 16 17) := do
  let ts ← TileSet.fromFile "puzzles/e2pieces.txt"
  match ts with
  | ⟨16, 17, tiles⟩ => return tiles
  | _ => panic! s!"e2pieces.txt has {ts.fst} size and {ts.snd.fst} colors??"

def signSols (ts : TileSet size colors) (reportProgress : Bool := false) : IO (List (TileSet size colors)) := do
  let (tsVars, enc) := EncCNF.new (do
    let tsVars ← Constraints.colorCardConstraints ts.tiles 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)

  -- Need a plain list of variables to check each time we solve
  let tsVars' := tsVars.map (·.2)

  return (← SATSolve.allSols enc tsVars' tsVars' reportProgress)
    |>.map fun sol =>
      ⟨ tsVars.map (fun (t,v) => { t with
          sign := sol.find? v
                  |>.map (fun | true => .plus | false => .minus)})
      ⟩

def decodeSol (tsv : Constraints.TileSetVariables size colors)
              (s : Std.AssocList EncCNF.Var Bool) :=
  show TileBoard size from {
    board :=
      Array.init _ (fun i =>
        Array.init _ (fun j =>
          List.fins _
            |>.find? (fun p => s.find? (tsv.piece_vars p ⟨i,j⟩) |>.get!)
            |>.map (tsv.tiles[·]!)
            |>.getD ⟨none,none,none,none,none⟩
      ))
    board_size := sorry
    isFinalized := true
    finalize := sorry
  }

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
  let size := 3
  let ts ← genTileSet size (size+2) 3
  IO.println ts

  let enc := EncCNF.new <| ExceptT.run do
    let tsv ← Constraints.puzzleConstraints ts
    match Constraints.tileIndices size.pred
              |>.find? (tsv.tiles[·]!.isCorner)
    with
    | none => return tsv
    | some p =>
    EncCNF.addClause [⟨tsv.piece_vars p ⟨0,0⟩, false⟩]
    return tsv

  match enc with
  | (.error s, _) => IO.println s!"failed to generate encoding: {s}"
  | (.ok tsv, enc) =>

  let sols ← SATSolve.allSols enc tsv.pieceVarList tsv.diamondVarList
  IO.println s!"{sols.length} total solutions"
  for s in sols do
    IO.println (decodeSol tsv s)

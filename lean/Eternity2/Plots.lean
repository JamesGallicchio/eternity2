import Eternity2.Puzzle

open Eternity2
open System


def genTileSet (size coreColors edgeColors : Nat)
  : IO (TileSet size (Color.withBorder edgeColors coreColors)) := do
  let b ← GenBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b
  return t.tileSet

def fetchEternity2Tiles : IO (TileSet 16 (Color.withBorder 5 17)) := do
  let ts ← TileSet.fromFile "../puzzles/e2pieces.txt"
  match ts with
  | ⟨16, 5, 17, tiles⟩ => return tiles
  | ⟨size,b,c,_⟩ => panic! s!"e2pieces.txt has size {size} and {b},{c} colors??"

/-
 - Generates boards of a specific size with a variety of colors and outputs
 -  and computes some metric with `calcData`
 -/
def plotData (name : String)
             (colLabels : List String)
             (size : Nat)
             (calcData : {b c : Nat}
                       → TileSet size (Color.withBorder b c)
                       → IO (List String))
           : IO Unit := do
  let plotsDir : FilePath := "./plots/"
  let outputFile : FilePath := plotsDir / s!"output_{name}_{size}.csv"
  let boardsDir : FilePath := plotsDir / "board"

  IO.FS.createDirAll boardsDir

  IO.FS.withFile outputFile .write (fun handle =>
   handle.putStrLn
     <| String.intercalate ","
     <| ["title", "size", "colors"] ++ colLabels
  )
  let maxColors := 7
  let maxRuns := 10
  parallel for i in [0:maxColors] do
    let colors := size + maxColors - i - 2
    parallel for j in [0:maxRuns] do
      let tiles ← genTileSet size colors (size.sqrt + 1)
      let boardTitle := s!"{size}_{colors}_{j}"

      IO.println s!"Board: {boardTitle}"

      let data ← calcData tiles

      IO.FS.withFile outputFile .append (fun handle => do
        handle.putStrLn
          <| String.intercalate ","
          <| [boardTitle, toString size, toString colors] ++ data
      )

def countSols (count : IO.Ref Nat)
              (output : Option ( FilePath
                               × Constraints.TileSetVariables size b c))
              (asgn : Std.HashMap EncCNF.Var Bool)
            : IO Unit := do
  count.modify (·+1)
  match output with
  | some (file, tsv) => (
    match SolvePuzzle.decodeTileBoard tsv asgn with
    | .ok tileboard => SolvePuzzle.writeSolution file tsv tileboard
    | .error s => panic! s
  )
  | none => return

def plotSolCounts (name : String)
                  (size : Nat)
                  (encoding : {b c : Nat}
                            → TileSet size (Color.withBorder b c)
                            → EncCNF (List EncCNF.Var))
                : IO Unit := do
  plotData name ["sols"] size @fun b c tiles => do
    let (blocking_vars, state) := EncCNF.new (encoding tiles)
    let count ← IO.mkRef 0

    SATSolve.allSols state (reportProgress := true) blocking_vars
      (perItem := @countSols size b c count none)

    return [toString <| ←count.get]


def plotSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "sign" size fun ts => do
    let tile_vars ← Constraints.colorCardConstraints ts.tiles
    return tile_vars.map (·.2)

def plotEdgeSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgesign" size fun ts => do
    let tile_vars ← Constraints.colorCardConstraints ts.tiles
    return tile_vars.filterMap (fun (t, v) =>
      if !t.isCenter then some v else none)

def plotPuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "puzzle" size fun ts => do
    match ← Constraints.puzzleConstraints ts with
    | .error s => panic! s!"it got sad :(\n{s}"
    | .ok tsv =>
      Constraints.fixCorner tsv
      return tsv.diamondVarList

def plotEdgePuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgepuzzle" size fun ts => do
    match ← Constraints.puzzleConstraints ts (onlyEdge := true) with
    | .error s => panic! s!"it got sad :(\n{s}"
    | .ok tsv =>
      Constraints.fixCorner tsv
      return tsv.borderDiamondVarList

def plotCorr_sign_puzzle_withTimes (size : Nat) : IO Unit := do
  plotData "corr_sign_puzzle_timed" ["signsols","puzzlesols","soltime","puzzlesols_withsigns","soltime_withsigns"]
    size @fun b c ts => do
      -- Count solutions to just polarity constraints
      let signsols ← (do
        let (blocking_vars, state) := EncCNF.new do
          let tile_vars ← Constraints.colorCardConstraints ts.tiles
          return tile_vars.map (·.2)

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := @countSols size b c count none)

        return ← count.get)

      -- Count solutions to just puzzle constraints (and time it)
      let (soltime, puzzlesols) ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new do
          match ← Constraints.puzzleConstraints ts with
          | .error s => panic! s!"it got sad :(\n{s}"
          | .ok tsv =>
            let () ← Constraints.fixCorner tsv
            return tsv.diamondVarList

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := fun _ => count.modify (·+1))
        
        return ← count.get)

      -- Count solutions to puzzle constraints with sign constraints (and time it)
      let (soltime_withsigns, puzzlesols') ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new do
          match ← Constraints.puzzleConstraints ts with
          | .error s => panic! s!"it got sad :(\n{s}"
          | .ok tsv =>
            let () ← Constraints.fixCorner tsv
            let vList ← Constraints.colorCardConstraints tsv.tiles
            let () ← Constraints.associatePolarities tsv vList sorry
            return tsv.diamondVarList

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := @countSols size b c count none)

        return ← count.get)

--      assert! (puzzlesols = puzzlesols')

      return  [ toString signsols
              , toString puzzlesols, toString soltime
              , toString puzzlesols', toString soltime_withsigns
              ]

def findEternityEdgeSols : IO Unit := do
  let e2 ← fetchEternity2Tiles
  match EncCNF.new do
    (Constraints.puzzleConstraints e2 (onlyEdge := true)).bind (m := EncCNF)
      (fun tsv => do
        Constraints.fixCorner tsv
        let vList ← Constraints.colorCardConstraints tsv.tiles
        let () ← Constraints.associatePolarities tsv vList sorry
        return tsv
      )
  with
  | (.error s, _) =>
    IO.println s!"Error building encoding: {s}"
  | (.ok tsv, state) =>
  let count ← IO.mkRef 0
  SATSolve.allSols state (reportProgress := true) tsv.diamondVarList (varsToBlock := tsv.borderDiamondVarList)
    (perItem := fun assn => do
      let i ← count.modifyGet (fun ct => (ct, ct + 1))
      let sol := SolvePuzzle.decodeDiamondBoard tsv assn
      IO.FS.createDirAll "border_sols/v2/"
      IO.FS.withFile s!"border_sols/v2/e2_border_sol_{i}.txt" .write (fun handle =>
        handle.putStrLn <| toString <| sol.tileBoard.mapColors (·.map (toString ·) |>.getD " ")
      )
    )



import Eternity2.FileFormat.Puz
import Eternity2.FileFormat.Sol
import Eternity2.Plots.BoardSuite
import Eternity2.Plots.GenRandom
import Eternity2.Puzzle.SolvePuzzle

namespace Eternity2

open System LeanSAT Encode

/- Runs `calcData` on the given board suite, outputting the
  results as CSV in the file `results`. -/
def plotData (name : String)
             (colLabels : List String)
             (suite : FilePath)
             (results : FilePath)
             (calcData : {size s : _}
                       → TileSet size (Tile <| Color.WithBorder s)
                       → IO (List String))
           : IO Unit := do
  -- load the board suite
  let suite ← BoardSuite.ofDirectory suite

  -- open results
  IO.FS.withFile results .write fun results => do
  
  -- print header
  results.putStrLn name
  results.putStrLn
     <| String.intercalate ","
     <| ["title", "size", "colors (center)", "colors (border)"] ++ colLabels

  -- run calcData in parallel across boards
  TaskIO.wait <| TaskIO.parTasksUnit suite.boards fun board => do
    let data ← calcData board.ts

    results.putStrLn
      <| String.intercalate ","
      <| [board.puzFile.toString, toString board.size,
          toString board.colors.center, toString board.colors.border]
          ++ data

variable [Solver.ModelCount IO]

def plotSolCounts (name suite results)
                  (encoding : {size s : _}
                            → TileSet size (Tile <| Color.WithBorder s)
                            → EncCNF (List Var))
                := show IO _ from do
  plotData name ["sol#"] suite results fun tiles => do
    let (blocking_vars, state) := EncCNF.new! (encoding tiles)
    let count ←
      Solver.ModelCount.modelCount
        state.toFormula
        blocking_vars

    return [toString count]


def plotSignSolCounts (suite output) := show IO _ from do
  plotSolCounts "sign" suite output fun ts => do
    let tsv ← Encoding.mkVars ts
    Encoding.colorCardConstraints tsv
    return tsv.signVarList

def plotEdgeSignSolCounts (suite output) := show IO _ from do
  plotSolCounts "edgesign" suite output fun ts => do
    let tsv ← Encoding.mkVars ts
    Encoding.colorCardConstraints tsv
    return List.fins _ |>.filterMap (fun i =>
      if !ts.tiles[ts.h_ts.symm ▸ i].isCenter
      then some (tsv.sign_vars i)
      else none)

def plotPuzzleSolCounts (suite output) := show IO _ from do
  plotSolCounts "puzzle" suite output fun ts => do
    let tsv ← Encoding.mkVars ts
    Encoding.compactEncoding tsv false
    --Encoding.fixCorner tsv
    return tsv.diamondVarList

def plotEdgePuzzleSolCounts (suite output) := show IO _ from do
  plotSolCounts "edgepuzzle" suite output fun ts => do
    let tsv ← Encoding.mkVars ts
    Encoding.compactEncoding tsv (onlyEdge := true)
    --Encoding.fixCorner tsv
    return tsv.borderDiamondVarList

def plotCorr_sign_puzzle_withTimes (suite output) := show IO _ from do
  plotData
    "corr_sign_puzzle_timed"
    ["signsols","puzzlesols","soltime","puzzlesols_withsigns","soltime_withsigns"]
    suite output
    fun ts => do
      -- Count solutions to just polarity constraints
      let signsols ← (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Encoding.mkVars ts
          Encoding.colorCardConstraints tsv
          return tsv.signVarList

        return ← Solver.ModelCount.modelCount
            state.toFormula blocking_vars)

      -- Count solutions to just puzzle constraints (and time it)
      let (soltime, puzzlesols) ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Encoding.mkVars ts
          Encoding.compactEncoding tsv
          --Encoding.fixCorner tsv
          return tsv.diamondVarList

        return ← Solver.ModelCount.modelCount
            state.toFormula blocking_vars)

      -- Count solutions to puzzle constraints with sign constraints (and time it)
      let (soltime_withsigns, puzzlesols') ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Encoding.mkVars ts
          Encoding.compactEncoding tsv
          --Encoding.fixCorner tsv
          Encoding.colorCardConstraints tsv
          Encoding.associatePolarities tsv
          return tsv.diamondVarList

        return ← Solver.ModelCount.modelCount
            state.toFormula blocking_vars)

--      assert! (puzzlesols = puzzlesols')

      return  [ toString signsols
              , toString puzzlesols, toString soltime
              , toString puzzlesols', toString soltime_withsigns
              ]

def testSolveTimes [Solver IO] (boardsuite : FilePath) (es : SolvePuzzle.EncodingSettings)
    : IO Unit := do
  IO.println "size,colors,iter,runtime(ms)"
  TaskIO.wait <| TaskIO.parUnit [4:17] fun size => do
    let mut colors := 5*size-15
    let mut decreasing := true
    while decreasing && colors ≥ size+1 do
      -- Solve each of the boards in this category
      let timedOut ← TaskIO.par [0:10] fun iter => do
        let ⟨_,_,ts⟩ ← FileFormat.TileSet.ofFile (
          boardsuite / s!"{size}" / s!"{colors}" / s!"board_{iter}.puz")
        let (tsv, enc) := EncCNF.new! <| SolvePuzzle.encodePuzzle ts es
        let startTime ← IO.monoMsNow
        let timedOut ←
          try (do let _ ← SolvePuzzle.solveAll enc tsv; return false)
          catch _ => pure true      
        let runtime := (←IO.monoMsNow) - startTime
        IO.println s!"{size},{colors},{iter},{runtime}"
        (←IO.getStdout).flush
        return timedOut

      -- If all boards in this category time out, stop decreasing
      if timedOut.all (·) then
        decreasing := false
      else
        colors := colors - 1

open Notation in
def getCorrs (enc : EncCNF.State) (tsv : Encoding.TileSetVariables (ts : TileSet size _))
  : IO (List (Fin (size*size) × Fin (size*size) × Nat × Nat)) := do
  let mut corrs := []
  for p1 in List.fins (size*size) do
    for p2 in List.fins (size*size) do
      if p1 ≥ p2 then
        continue
      let signVars := tsv.signVarList
      let ((),sameEnc) := EncCNF.run! enc do
        EncCNF.addClause (¬tsv.sign_vars p1 ∨ tsv.sign_vars p2)
        EncCNF.addClause (¬tsv.sign_vars p2 ∨ tsv.sign_vars p1)
      let ((), diffEnc) := EncCNF.run! enc do
        EncCNF.addClause (tsv.sign_vars p1 ∨ tsv.sign_vars p2)
        EncCNF.addClause (¬tsv.sign_vars p1 ∨ ¬tsv.sign_vars p2)
      let same_count ← Solver.ModelCount.modelCount sameEnc.toFormula signVars
      let diff_count ← Solver.ModelCount.modelCount diffEnc.toFormula signVars
      corrs := (p1,p2,same_count,diff_count) :: corrs
  return corrs

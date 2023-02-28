import Eternity2.FileFormat.Puz
import Eternity2.FileFormat.Sol
import Eternity2.Plots.BoardSuite
import Eternity2.Plots.GenRandom
import Eternity2.Puzzle.SolvePuzzle
import SolverConfig

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

def plotSolCounts (name suite results)
                  (encoding : {size s : _}
                            → TileSet size (Tile <| Color.WithBorder s)
                            → EncCNF (List Var))
                := show IO _ from do
  plotData name ["sol#"] suite results fun tiles => do
    let (blocking_vars, state) := EncCNF.new! (encoding tiles)
    let count ←
      Solver.ApproxModelCount.approxModelCount
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
      if !tsv.ts.tiles[tsv.ts.h_ts.symm ▸ i].isCenter
      then some (tsv.sign_vars i)
      else none)

def plotPuzzleSolCounts (suite output) := show IO _ from do
  plotSolCounts "puzzle" suite output fun ts => do
    let tsv ← Encoding.mkVars ts
    Encoding.compactEncoding tsv false
    Encoding.fixCorner tsv
    return tsv.diamondVarList

def plotEdgePuzzleSolCounts (suite output) := show IO _ from do
  plotSolCounts "edgepuzzle" suite output fun ts => do
    let tsv ← Encoding.mkVars ts
    Encoding.compactEncoding tsv (onlyEdge := true)
    Encoding.fixCorner tsv
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

        return ← Solver.ApproxModelCount.approxModelCount
            state.toFormula blocking_vars)

      -- Count solutions to just puzzle constraints (and time it)
      let (soltime, puzzlesols) ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Encoding.mkVars ts
          Encoding.compactEncoding tsv
          Encoding.fixCorner tsv
          return tsv.diamondVarList

        return ← Solver.ApproxModelCount.approxModelCount
            state.toFormula blocking_vars)

      -- Count solutions to puzzle constraints with sign constraints (and time it)
      let (soltime_withsigns, puzzlesols') ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Encoding.mkVars ts
          Encoding.compactEncoding tsv
          Encoding.fixCorner tsv
          Encoding.colorCardConstraints tsv
          Encoding.associatePolarities tsv
          return tsv.diamondVarList

        return ← Solver.ApproxModelCount.approxModelCount
            state.toFormula blocking_vars)

--      assert! (puzzlesols = puzzlesols')

      return  [ toString signsols
              , toString puzzlesols, toString soltime
              , toString puzzlesols', toString soltime_withsigns
              ]

/- Outputs all solutions to a given tileset as solution files in `outputFolder`. -/
def outputAllSols (name : String) (ts : TileSet size (Tile <| Color.WithBorder s))
      (outputFolder : FilePath)
      (es : SolvePuzzle.EncodingSettings)
      (parallelize : Bool := false)
      : Log TaskIO Unit
  := do
  let (tsv, enc) := EncCNF.new! <| SolvePuzzle.encodePuzzle ts es
  IO.FS.withFile (outputFolder / s!"{name}.cnf") .write fun handle =>
    Solver.Dimacs.printEnc handle.putStrLn enc
  let counter ← IO.mkRef 0
  if parallelize then
    fun handle => do
    TaskIO.parUnit (List.fins 6) fun i => do
      Log.run handle do
      let ((), enc) := EncCNF.run! enc do
        Encoding.fixCorners tsv i
      Log.info s!"Board {name} c{i}: Starting solver"
      solveAndOutput tsv enc s!"{name} c{i}" counter
      Log.info s!"Board {name} c{i}: Solver finished"
  else
    let ((), enc) := EncCNF.run! enc do
      Encoding.fixCorner tsv
    solveAndOutput tsv enc name counter
  IO.FS.writeFile (outputFolder / "done") ""
  Log.info s!"Board {name}: All solutions found"
where
  solveAndOutput tsv enc name counter : Log IO _ := fun handle => do
    let sols ← Solver.allSolutions enc.toFormula tsv.diamondVarList
    for assn in sols do
      Log.run handle do
        let num ← counter.modifyGet (fun i => (i,i+1))
        Log.info s!"Board {name}: Found solution #{num}"
        match SolvePuzzle.decodeSol tsv assn with
        | .error s =>
          Log.error s!"Failed to decode board {name} solution #{num}: {s}"
        | .ok sol =>
        let file := outputFolder / s!"{name}_sol{num}.sol"
        FileFormat.BoardSol.toFile file sol
        Log.info s!"Board {name}: Wrote solution #{num} to {file}"


def testSolveTimes (boardsuite : FilePath) (timeout : Nat)
    (es : SolvePuzzle.EncodingSettings)
    : IO Unit := do
  IO.println "size,colors,iter,runtime(ms)"
  TaskIO.wait <| TaskIO.parUnit [4:17] fun size => do
    let mut colors := 5*size-15
    let mut decreasing := true
    while decreasing && colors ≥ size+1 do
      -- Solve each of the boards in this category
      let timedOut ← TaskIO.parTasks [0:10] fun iter => do
        let ⟨_,_,ts⟩ ← FileFormat.TileSet.ofFile (
          boardsuite / s!"{size}" / s!"{colors}" / s!"board_{iter}.puz")
        let (tsv, enc) := EncCNF.new! <| SolvePuzzle.encodePuzzle ts es
        let startTime ← IO.monoMsNow
        let timedOut :=
          match ← (IO.asTaskTimeout timeout <| SolvePuzzle.solveAll enc tsv) with
          | .ok _ => false
          | .error () => true      
        let runtime := (←IO.monoMsNow) - startTime
        IO.println s!"{size},{colors},{iter},{runtime}"
        (←IO.getStdout).flush
        return timedOut

      -- If all boards in this category time out, stop decreasing
      if timedOut.all (·) then
        decreasing := false
      else
        colors := colors - 1

open Notation in -- nice notation for encodings
def getCorrs (enc : EncCNF.State) (tsv : Encoding.TileSetVariables size s)
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
      let same_count ← Solver.ApproxModelCount.approxModelCount sameEnc.toFormula signVars
      let diff_count ← Solver.ApproxModelCount.approxModelCount diffEnc.toFormula signVars
      corrs := (p1,p2,same_count.toNat,diff_count.toNat) :: corrs
  return corrs

partial def findCorrs (ts : TileSet size (Tile <| Color.WithBorder s)) (sols : List (BoardSol ts)) : IO Unit := do
  let (tsv, enc) := EncCNF.new! do
    let tsv ← Encoding.mkVars ts
    Encoding.colorCardConstraints tsv
    Encoding.signCardConstraints tsv
    if h:0 < size*size then EncCNF.addClause (tsv.sign_vars ⟨0,h⟩)
    return tsv

  let mut enc := enc

  let mut assigned := []
  while true do
    let corrs ← getCorrs enc tsv
    let guess := corrs.foldl (fun acc (p1,p2,s,d) =>
      match acc with
      | none =>
        if !assigned.contains (p1,p2)
        then some (p1,p2,s,d)
        else none
      | some (_,_,ms,md) =>
        if !assigned.contains (p1,p2) && min s d < min ms md
        then some (p1,p2,s,d)
        else acc
    ) none
    match guess with
    | none =>
      break
    | some (p1,p2, same,diff) =>
      let pct := (Nat.toFloat <| min same diff) / (Nat.toFloat <| same + diff)
      let actSame :=
        sols.countp (fun sol =>
            let (q1,_) := sol.pieceIdx p1
            let (q2,_) := sol.pieceIdx p2
            (q1.row + q1.col + q2.row + q2.col : Nat) % 2 == 0)
      let actDiff := sols.length - actSame

      let (p1v, p2v) := (tsv.sign_vars p1, tsv.sign_vars p2)
      IO.println s!"({assigned.length})\t{p1} {p2}: {same}, {diff} ({pct*100}%); actual {actSame}, {actDiff}"
      if same > diff then
        IO.println s!"\tAssigning {p1}, {p2} to be the same.\t(matches {actSame} sols)"
        enc := (·.2) <| EncCNF.run! enc do
          EncCNF.addClause ⟨[.not p1v, p2v]⟩ 
          EncCNF.addClause ⟨[p1v, .not p2v]⟩ 
      else
        IO.println s!"\tAssigning {p1}, {p2} to be different.\t(matches {actDiff} sols)"
        enc := (·.2) <| EncCNF.run! enc do
          EncCNF.addClause ⟨[p1v, p2v]⟩
          EncCNF.addClause ⟨[.not p1v, .not p2v]⟩
      assigned := (p1, p2) :: assigned

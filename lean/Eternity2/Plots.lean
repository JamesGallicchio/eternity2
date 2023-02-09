import Eternity2.Puzzle

open Eternity2
open System
open LeanSAT Encode


def genTileSet (size coreColors edgeColors : Nat)
  : IO (TileSet size (Color.withBorder edgeColors coreColors)) := do
  let b ← GenBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b
  let ⟨ts,_⟩ ← t.toBoardSol.2.scramble
  return ts

def fetchEternity2Tiles : IO (TileSet 16 (Color.withBorder 5 17)) := do
  let ts ← TileSet.fromFile "../puzzles/e2pieces.txt"
  match ts with
  | ⟨16, 5, 17, tiles⟩ => return tiles
  | ⟨size,b,c,_⟩ => panic! s!"e2pieces.txt has size {size} and {b},{c} colors??"

/-
Generates boards of a specific size with a variety of colors and outputs
and computes some metric with `calcData`
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
  TaskIO.wait <| TaskIO.parUnit [0:maxColors] fun i => do
    let colors := size + maxColors - i - 2
    TaskIO.parTasksUnit [0:maxRuns] fun j => do
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
              (asgn : Std.HashMap Var Bool)
            : IO Unit := do
  count.modify (·+1)
  match output with
  | some (file, tsv) => (
    match SolvePuzzle.decodePieces tsv asgn with
    | .ok sol => sol.writeSolution file
    | .error s => panic! s
  )
  | none => return

def plotSolCounts (name : String)
                  (size : Nat)
                  (encoding : {b c : Nat}
                            → TileSet size (Color.withBorder b c)
                            → EncCNF (List Var))
                : IO Unit := do
  plotData name ["sols"] size fun tiles => do
    let (blocking_vars, state) := EncCNF.new! (encoding tiles)
    let count ←
      Solver.ApproxModelCount.approxModelCount
        state.toFormula
        blocking_vars

    return [toString count]


def plotSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "sign" size fun ts => do
    let tsv ← Constraints.mkVars ts
    Constraints.colorCardConstraints tsv
    return tsv.signVarList

def plotEdgeSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgesign" size fun ts => do
    let tsv ← Constraints.mkVars ts
    Constraints.colorCardConstraints tsv
    return List.fins _ |>.filterMap (fun i =>
      if !tsv.ts.tiles[tsv.ts.h_ts.symm ▸ i].isCenter
      then some (tsv.sign_vars i)
      else none)

def plotPuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "puzzle" size fun ts => do
    let tsv ← Constraints.mkVars ts
    Constraints.compactEncoding tsv false
    Constraints.fixCorner tsv
    return tsv.diamondVarList

def plotEdgePuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgepuzzle" size fun ts => do
    let tsv ← Constraints.mkVars ts
    Constraints.compactEncoding tsv (onlyEdge := true)
    Constraints.fixCorner tsv
    return tsv.borderDiamondVarList

def plotCorr_sign_puzzle_withTimes (size : Nat) : IO Unit := do
  plotData "corr_sign_puzzle_timed" ["signsols","puzzlesols","soltime","puzzlesols_withsigns","soltime_withsigns"]
    size @fun b c ts => do
      -- Count solutions to just polarity constraints
      let signsols ← (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Constraints.mkVars ts
          Constraints.colorCardConstraints tsv
          return tsv.signVarList

        return ← Solver.ApproxModelCount.approxModelCount
            state.toFormula blocking_vars)

      -- Count solutions to just puzzle constraints (and time it)
      let (soltime, puzzlesols) ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Constraints.mkVars ts
          Constraints.compactEncoding tsv
          Constraints.fixCorner tsv
          return tsv.diamondVarList

        return ← Solver.ApproxModelCount.approxModelCount
            state.toFormula blocking_vars)

      -- Count solutions to puzzle constraints with sign constraints (and time it)
      let (soltime_withsigns, puzzlesols') ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Constraints.mkVars ts
          Constraints.compactEncoding tsv
          Constraints.fixCorner tsv
          Constraints.colorCardConstraints tsv
          Constraints.associatePolarities tsv
          return tsv.diamondVarList

        return ← Solver.ApproxModelCount.approxModelCount
            state.toFormula blocking_vars)

--      assert! (puzzlesols = puzzlesols')

      return  [ toString signsols
              , toString puzzlesols, toString soltime
              , toString puzzlesols', toString soltime_withsigns
              ]


/- Outputs all solutions to a given tileset as solution files in `outputFolder`. -/
def outputAllSols (name : String) (ts : TileSet size (Color.withBorder b c))
      (outputFolder : FilePath)
      (es : EncodingSettings)
      (parallelize : Bool := false)
      : Log TaskIO Unit
  := do
  let (tsv, enc) := EncCNF.new! <| encodePuzzle ts es
  IO.FS.withFile (outputFolder / s!"{name}.cnf") .write fun handle =>
    Solver.Dimacs.printEnc handle.putStrLn enc
  let counter ← IO.mkRef 0
  if parallelize then
    fun handle => do
    TaskIO.parUnit (List.fins 6) fun i => do
      Log.run handle do
      let ((), enc) := EncCNF.run! enc do
        Constraints.fixCorners tsv i
      Log.info s!"Board {name} c{i}: Starting solver"
      solveAndOutput tsv enc s!"{name} c{i}" counter
      Log.info s!"Board {name} c{i}: Solver finished"
  else
    let ((), enc) := EncCNF.run! enc do
      Constraints.fixCorner tsv
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
        match SolvePuzzle.decodePieces tsv assn with
        | .error s =>
          Log.error s!"Failed to decode board {name} solution #{num}: {s}"
        | .ok sol =>
        let file := outputFolder / s!"{name}_sol{num}.sol"
        sol.writeSolution file
        Log.info s!"Board {name}: Wrote solution #{num} to {file}"

def genAndSolveBoards (outputDir : FilePath)
                      (size colors count : Nat)
    : Log TaskIO Unit := do
  Log.info s!"Output directory: {outputDir}"
  fun handle => do
  TaskIO.parUnit [0:count] fun rep => do
    Log.run handle do
    let name := s!"tiles_{size}_{colors}__{rep}"
    Log.info s!"Generating tile set {name}"
    let ts ← genTileSet size colors (Nat.sqrt size + 1)
    let file := outputDir / s!"{name}.tiles"
    Log.info s!"Generated tile set {name}"
    ts.toFile file
    let solDir := outputDir / name
    IO.FS.createDir solDir
    Log.info s!"Finding solutions to {name}"
    outputAllSols name ts solDir (parallelize := true) {}




def genBoardSuite (output : FilePath) : IO Unit := do
  for size in [4:17] do
    IO.FS.createDir (output / s!"{size}")
    for colors in [size+1:101] do
      IO.FS.createDir (output / s!"{size}" / s!"{colors}")
      for iter in [0:10] do
        let b ← GenBoard.generate size colors (Nat.sqrt size + 1)
        let t := DiamondBoard.tileBoard b
        let ⟨ts,b⟩ ← t.toBoardSol.2.scramble
        IO.FS.createDir (output / s!"{size}" / s!"{colors}" / s!"board_{iter}")
        b.writeSolution (output / s!"{size}" / s!"{colors}" / s!"board_{iter}" / "default_sol.sol")
        ts.toFile (output / s!"{size}" / s!"{colors}" / s!"board_{iter}.puz")


def testSolveTimes (boardsuite : FilePath) (timeout : Nat)
    (es : EncodingSettings)
    : IO Unit := do
  IO.println "size,colors,iter,runtime(ms)"
  TaskIO.wait <| TaskIO.parUnit [4:17] fun size => do
    let mut colors := 5*size-15
    let mut decreasing := true
    while decreasing && colors ≥ size+1 do
      -- Solve each of the boards in this category
      let timedOut ← TaskIO.parTasks [0:10] fun iter => do
        let ⟨_,_,_,ts⟩ ← TileSet.fromFile (
          boardsuite / s!"{size}" / s!"{colors}" / s!"board_{iter}.puz")
        let (tsv, enc) := EncCNF.new! <| encodePuzzle ts es
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
def getCorrs (enc : EncCNF.State) (tsv : Constraints.TileSetVariables size b c)
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

partial def findCorrs (ts : TileSet size (Color.withBorder b c)) (sols : List (BoardSol ts)) : IO Unit := do
  let (tsv, enc) := EncCNF.new! do
    let tsv ← Constraints.mkVars ts
    Constraints.colorCardConstraints tsv
    Constraints.signCardConstraints tsv
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

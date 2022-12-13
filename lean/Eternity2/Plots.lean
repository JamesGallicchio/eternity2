import Eternity2.Puzzle

open Eternity2
open System


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
              (asgn : Std.HashMap EncCNF.Var Bool)
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
                            → EncCNF (List EncCNF.Var))
                : IO Unit := do
  plotData name ["sols"] size @fun b c tiles => do
    let (blocking_vars, state) := EncCNF.new! (encoding tiles)
    let count ← IO.mkRef 0

    SATSolve.allSols state (reportProgress := true) blocking_vars
      (perItem := @countSols size b c count none)

    return [toString <| ←count.get]


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

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := @countSols size b c count none)

        return ← count.get)

      -- Count solutions to just puzzle constraints (and time it)
      let (soltime, puzzlesols) ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Constraints.mkVars ts
          Constraints.compactEncoding tsv
          Constraints.fixCorner tsv
          return tsv.diamondVarList

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := fun _ => count.modify (·+1))
        
        return ← count.get)

      -- Count solutions to puzzle constraints with sign constraints (and time it)
      let (soltime_withsigns, puzzlesols') ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new! do
          let tsv ← Constraints.mkVars ts
          Constraints.compactEncoding tsv
          Constraints.fixCorner tsv
          Constraints.colorCardConstraints tsv
          Constraints.associatePolarities tsv
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
  match EncCNF.new? do
    let tsv ← Constraints.mkVars e2
    Constraints.compactEncoding tsv (onlyEdge := true)
    Constraints.fixCorner tsv
    Constraints.colorCardConstraints tsv
    Constraints.associatePolarities tsv
    return tsv
  with
  | .error s =>
    IO.println s!"Error building encoding: {s}"
  | .ok (tsv, state) =>
  let count ← IO.mkRef 0
  SATSolve.allSols state (reportProgress := true) tsv.diamondVarList (varsToBlock := tsv.borderDiamondVarList)
    (perItem := fun assn => do
      let i ← count.modifyGet (fun ct => (ct, ct + 1))
      let sol := SolvePuzzle.decodeDiamonds tsv assn
      IO.FS.createDirAll "border_sols/v2/"
      /- TODO: Better output format here -/
      IO.FS.withFile s!"border_sols/v2/e2_border_sol_{i}.txt" .write (fun handle =>
        handle.putStrLn <| toString <| sol.tileBoard.mapColors (·.map (toString ·) |>.getD " ")
      )
    )


/- Outputs all solutions to a given tileset as solution files in `outputFolder`. -/
def outputAllSols (name : String) (ts : TileSet size (Color.withBorder b c))
      (outputFolder : FilePath)
      (es : EncodingSettings)
      (parallelize : Bool := false)
      : Log TaskIO Unit
  := do
  match EncCNF.new? <| encodePuzzle ts es with
  | .error s =>
    Log.error s!"outputAllSols aborting on board {name}\nfailed to encode tileset. error:\n{s}"
  | .ok (tsv, enc) =>
  IO.FS.withFile (outputFolder / s!"{name}.cnf") .write fun handle =>
    enc.printAux handle.putStrLn
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
    SATSolve.allSols enc
      (tsv.pieceVarList ++ tsv.diamondVarList)
      tsv.diamondVarList
      (perItem := fun assn => Log.run handle do
        let num ← counter.modifyGet (fun i => (i,i+1))
        Log.info s!"Board {name}: Found solution #{num}"
        match SolvePuzzle.decodePieces tsv assn with
        | .error s =>
          Log.error s!"Failed to decode board {name} solution #{num}: {s}"
        | .ok sol =>
        let file := outputFolder / s!"{name}_sol{num}.sol"
        sol.writeSolution file
        Log.info s!"Board {name}: Wrote solution #{num} to {file}"
      )

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
    (es : EncodingSettings) (useSolSigns : Bool := false)
    : IO Unit := do
  let es := if useSolSigns then {es with usePolarity := false} else es
  IO.println "size,colors,iter,runtime(ms)"
  TaskIO.wait <| TaskIO.parUnit [4:17] fun size => do
    let mut colors := 5*size-15
    let mut decreasing := true
    while decreasing && colors ≥ size+1 do
      -- Solve each of the boards in this category
      let timedOut ← TaskIO.parTasks [0:10] fun iter => do
        let ⟨_,_,_,ts⟩ ← TileSet.fromFile (
          boardsuite / s!"{size}" / s!"{colors}" / s!"board_{iter}.puz")
        match EncCNF.new? <| encodePuzzle ts es with
        | .error s =>
          IO.println s!"Encoding board {size}/{colors}/board_{iter}.puz failed: {s}"
          return true
        | .ok (tsv, enc) =>
        /- Add the solution's signs, if desired -/
        let ((), enc) ← if !useSolSigns then pure ((), enc) else do
          let sol ← BoardSol.readSolution
            (boardsuite / s!"{size}" / s!"{colors}" / s!"board_{iter}" / "default_sol.sol")
            tsv.ts
          let signsol := SignSol.ofSol tsv.ts sol
          pure <| EncCNF.run! enc do
            Constraints.associatePolarities tsv
            Constraints.signSolConstraints tsv signsol
        let startTime ← IO.monoMsNow
        let timedOut ← IO.mkRef false
        let _ ← SolvePuzzle.solveAll enc tsv (termCond := some do
          let willTimeOut := (←IO.monoMsNow) > startTime + timeout
          if willTimeOut then
            timedOut.set true
          return willTimeOut)        
        let runtime := (←IO.monoMsNow) - startTime
        IO.println s!"{size},{colors},{iter},{runtime}"
        (←IO.getStdout).flush
        return ←timedOut.get

      -- If all boards in this category time out, stop decreasing
      if timedOut.all (·) then
        decreasing := false
      else
        colors := colors - 1

def getCorrs (enc : EncCNF.State) (tsv : Constraints.TileSetVariables size b c) (iters timeout : Nat) : IO (List (SquareIndex size × SquareIndex size × Nat × Nat)) := do
  let signsols ← (do
    let mut signsols ← IO.mkRef []
    for i in [0:iters] do
      let enc ← enc.scramble
      let start ← IO.monoMsNow
      let count ← IO.mkRef 0
      let () ← SATSolve.allSols enc tsv.signVarList
        (termCond := some (do
          let now := (← IO.monoMsNow)
          let doTimeout := (start + timeout) < now
          if doTimeout then
            IO.println s!"timing out iteration {i} after finding {←count.get} sols"
            (←IO.getStdout).flush
          return doTimeout
          ))
        (perItem := fun assn => do
          count.modify (· + 1)
          signsols.modify (assn :: ·))
    signsols.get)

  let corrs :=
    SquareIndex.all size |>.bind fun p1 =>
    SquareIndex.all size |>.bind fun p2 =>
    let idx1 := SquareIndex.toFin p1
    let idx2 := SquareIndex.toFin p2
    if idx1 ≥ idx2 then []
    else [
      let sameCount :=
        signsols.countp (fun assn =>
          assn.find? (tsv.sign_vars idx1) == assn.find? (tsv.sign_vars idx2))
      let diffCount :=
        signsols.countp (fun assn =>
          assn.find? (tsv.sign_vars idx1) != assn.find? (tsv.sign_vars idx2))
      (p1, p2, sameCount, diffCount)
    ]
  return corrs

partial def findCorrs (ts : TileSet size (Color.withBorder b c)) (iters timeout : Nat) : IO Unit := do
  match EncCNF.new? do
    let tsv ← Constraints.mkVars ts
    Constraints.colorCardConstraints tsv
    Constraints.signCardConstraints tsv
    if h:0 < size*size then EncCNF.addClause [tsv.sign_vars ⟨0,h⟩]
    return tsv
  with
  | .error s => panic! s!"failed to encode: {s}"
  | .ok (tsv, enc) =>
  let mut enc := enc
  let boardSols ← (do
    let mut boardSols ← IO.mkRef []
    match EncCNF.new? <| encodePuzzle ts {} with
    | .error s =>
      IO.println s!"aborting, failed to encode tileset. error:\n{s}"
    | .ok (tsv, enc) =>
      SATSolve.allSols enc
        (tsv.pieceVarList ++ tsv.diamondVarList)
        tsv.diamondVarList
        (perItem := fun assn => do
          let poses : Fin size → Fin size → SquareIndex size := fun i j =>
              let idx1 := SquareIndex.toFin ⟨i,j⟩
              match
                List.find?
                  (assn.find! <| tsv.piece_vars idx1 ·)
                  (SquareIndex.all size)
              with
              | some x => x
              | none =>
                letI : Inhabited (SquareIndex size) := (match size, i with | 0, i => i.elim0 | _+1, _ => ⟨⟨0,0⟩⟩)
                panic! "piece not placed?"
          boardSols.modify (poses :: ·)
        )
    return ←boardSols.get)

  IO.println ts
  IO.println ""

  for sol in boardSols do
    for i in List.fins _ do
      for j in List.fins _ do
        IO.print (sol i j)
        IO.print " "
      IO.println ""
    IO.println ""

  let mut assigned := []
  while true do
    let corrs ← getCorrs enc tsv iters timeout
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
        boardSols.countp (fun placement =>
            let q1 := placement p1.1 p1.2
            let q2 := placement p2.1 p2.2
            (q1.row + q1.col + q2.row + q2.col : Nat) % 2 == 0)
      let actDiff :=
        boardSols.countp (fun placement =>
            let q1 := placement p1.1 p1.2
            let q2 := placement p2.1 p2.2
            (q1.row + q1.col + q2.row + q2.col : Nat) % 2 == 1)

      let (p1v, p2v) := (tsv.sign_vars p1.toFin, tsv.sign_vars p2.toFin)
      IO.println s!"({assigned.length})\t{p1} {p2}: {same}, {diff} ({pct*100}%); actual {actSame}, {actDiff}"
      if same > diff then
        IO.println s!"\tAssigning {p1}, {p2} to be the same.\t(matches {actSame} sols)"
        enc := (·.2) <| EncCNF.run! enc do
          EncCNF.addClause [.not p1v, p2v]
          EncCNF.addClause [p1v, .not p2v]
      else
        IO.println s!"\tAssigning {p1}, {p2} to be different.\t(matches {actDiff} sols)"
        enc := (·.2) <| EncCNF.run! enc do
          EncCNF.addClause [p1v, p2v]
          EncCNF.addClause [.not p1v, .not p2v]
      assigned := (p1, p2) :: assigned

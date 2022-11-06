import Eternity2

open Eternity2

def genTileSet (size coreColors edgeColors : Nat) : IO TileSet := do
  let b ← DiamondBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b false
  IO.println t
  return t.tileSet

def fetchEternity2Tiles : IO TileSet :=
  TileSet.fromFile "puzzles/e2pieces.txt"

def signSols (ts : TileSet) (reportProgress : Bool := false) : IO (List TileSet) := do
  IO.FS.createDirAll "cnf"
  let tempFileName := s!"cnf/temp{←IO.rand 1 10000}.cnf"
  let (tsVars, enc) := EncCNF.new (do
    let tsVars ← Constraints.colorCardConstraints ts.tiles 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)

  -- Need a plain list of variables to check each time we solve
  let tsVars' := tsVars.map (·.2)

  enc.printFileDIMACS tempFileName

  let mut count := 0
  let mut sols := []
  let mut satResult := SATSolve.solve enc tsVars'

  let start ← IO.monoMsNow
  let mut lastUpdateTime := 0

  while satResult.isSome do
    let now ← IO.monoMsNow
    if reportProgress && now - lastUpdateTime > 2000 then
      lastUpdateTime := now
      IO.print s!"\rfound {count} ({count*1000/(now-start)} / sec)"
      (←IO.getStdout).flush

    match satResult with
    | none => panic! "Unreachable :( 12509814"
    | some (s, assn) =>
      count := count + 1
      let sol :=
        ⟨ tsVars.map (fun (t,v) =>
            {t with sign := assn.find? v |>.map (fun | true => .plus | false => .minus)})
        , ts.size⟩
      sols := sol :: sols
      let newClause : EncCNF.Clause :=
        tsVars.map (fun (_,v) => ⟨v, assn.find? v |>.get!⟩)
      enc.appendFileDIMACSClause tempFileName newClause

      satResult := SATSolve.addAndResolve s newClause tsVars'

  if reportProgress then
    let duration := (←IO.monoMsNow) - start
    IO.println s!"\rfound {count} solutions in {duration}ms ({(1000*count)/duration} / sec)"
    (←IO.getStdout).flush

  IO.FS.removeFile tempFileName
  return sols

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

def main : IO Unit := do
  let ts ← genTileSet 6 7 3
  let _ ← signSols ts (reportProgress := true)

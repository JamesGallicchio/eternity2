import Eternity2

open Eternity2

def genTileSet (size colors : Nat) : IO TileSet := do
  let b ← DiamondBoard.generate size colors
  let t := DiamondBoard.tileBoard b false
  return t.tileSet

def fetchEternity2Tiles : IO TileSet :=
  TileSet.fromFile "puzzles/e2pieces.txt"

def signSols (ts : TileSet) (reportProgress : Bool := false) : IO (List TileSet) := do
  IO.FS.createDirAll "cnf"
  let tempFileName := s!"cnf/temp{←IO.monoMsNow}{←IO.rand 1000 9999}.cnf"
  let (tsVars, enc) := EncCNF.new (do
    let tsVars ← Constraints.colorCardConstraints ts.tiles 9
    EncCNF.addClause [⟨tsVars.head!.2, false⟩]
    return tsVars)
  
  -- Need a plain list of variables to check each time we solve
  let tsVars' := tsVars.map (·.2)

  enc.printFileDIMACS tempFileName

  let mut done := false
  let mut count := 0
  let mut sols := []
  let mut enc' := enc

  let start ← IO.monoMsNow
  let mut lastUpdateTime := 0

  while !done do
    let now ← IO.monoMsNow
    if reportProgress && now - lastUpdateTime > 2000 then
      lastUpdateTime := now
      IO.print s!"\rfound {count} ({count*1000/(now-start)} / sec)"
      (←IO.getStdout).flush

    match SATSolve.solve enc' tsVars' with
    | none => done := true
    | some as =>
      count := count + 1
      let sol :=
        ⟨ tsVars.map (fun (t,v) =>
            {t with sign := as.find? v |>.map (fun | true => .plus | false => .minus)})
        , ts.size⟩
      sols := sol :: sols
      let newClause : EncCNF.Clause :=
        tsVars.map (fun (_,v) => ⟨v, as.find? v |>.get!⟩)
      enc.appendFileDIMACSClause tempFileName newClause
      enc' := EncCNF.run enc' (EncCNF.addClause newClause) |>.2

  if reportProgress then
    let duration := (←IO.monoMsNow) - start
    IO.println s!"\rfound {count} solutions in {duration / 1000}.{duration % 10000}s ({(1000*count)/duration} / sec)"
    (←IO.getStdout).flush
  
  IO.FS.removeFile tempFileName
  return sols

section variable (size : Nat) (iters := 100) (reportProgress := true)

def sampleSolutionCounts : IO (List Nat) := do
  let counts : IO.Ref (List Nat) ← IO.mkRef []
  let width := 80
  IO.print ("[".pushn ' ' width ++ "]")
  for i in [0:iters] do
    if reportProgress then
      let stars := (width * i + width / 2 + 1) / iters
      IO.print ("\r[".pushn '*' stars |>.pushn ' ' (width-stars) |>.push ']')
      (←IO.getStdout).flush
    let ts ← genTileSet size size
    let sols ← signSols ts
    counts.modify (sols.length :: ·)

  IO.println <| "\r".pushn ' ' width
  return ← counts.get

def parSampleSolutionCounts (resfile : String) : IO Unit := do
  parallel for i in [0:iters] do
    let ts ← genTileSet size size
    let sols ← signSols ts
    IO.FS.withFile resfile .append (fun handle =>
      handle.putStrLn s!"{sols.length}")

def printSolutionCountStats := do
  let counts := 
    (← sampleSolutionCounts size iters reportProgress)
    |> Array.mk
    |>.insertionSort (· < ·)
  IO.println s!"size: {size}"
  IO.println s!"counts: {counts}"
  let avg := (counts.foldl (· + ·) (counts.size / 2)) / counts.size
  let var := (counts.foldl (fun acc x => acc + (x - avg) * (x - avg)) (counts.size / 2)) / counts.size
  let min := counts[0]!
  let max := counts[counts.size-1]!
  let median :=
    (counts[counts.size / 2]! + counts[(counts.size+1) / 2]!) / 2
  IO.println s!"avg: {avg}"
  IO.println s!"var: {var}"
  IO.println s!"std: {Nat.sqrt var}"
  IO.println s!"min: {min}"
  IO.println s!"med: {median}"
  IO.println s!"max: {max}"

end

set_option compiler.extract_closed false in
def main : IO Unit := do
  let ts ← genTileSet 6 6
  let _ ← signSols ts (reportProgress := true)

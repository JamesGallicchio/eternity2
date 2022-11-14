import Cli
import Eternity2

open Eternity2
open System

def genTileSet (size coreColors edgeColors : Nat) : IO (TileSet size coreColors) := do
  let b ← DiamondBoard.generate size coreColors edgeColors
  let t := DiamondBoard.tileBoard b false
  return t.tileSet coreColors

def fetchEternity2Tiles : IO (TileSet 16 22) := do
  let ts ← TileSet.fromFile "../puzzles/e2pieces.txt"
  match ts with
  | ⟨16, 22, tiles⟩ => return tiles
  | ⟨size,colors,_⟩ => panic! s!"e2pieces.txt has size {size} and {colors} colors??"

def plotData (name : String) (colLabels : List String) (size : Nat)
  (calcData : (colors : Nat) → TileSet size colors → IO (List String)) : IO Unit := do
  let plotsDir : FilePath := "./plots/"
  let outputFile : FilePath := plotsDir / s!"output_{name}_{size}.csv"
  let boardsDir : FilePath := plotsDir / "board"

  IO.FS.createDirAll boardsDir

  IO.FS.withFile outputFile .write (fun handle =>
    handle.putStrLn
      <| String.intercalate ","
      <| ["title", "size", "colors"] ++ colLabels
  )
  for i in [0:10] do
    let colors := size + i
    parallel for j in [0:10] do
      let tiles ← genTileSet size colors (size.sqrt + 1)
      let boardTitle := s!"{size}_{colors}_{j}"

      IO.println s!"Board: {boardTitle}"

      let data ← calcData colors tiles

      IO.FS.withFile outputFile .append (fun handle => do
        handle.putStrLn
          <| String.intercalate ","
          <| [boardTitle, toString size, toString colors] ++ data
      )

def plotSolCounts (name : String) (size : Nat)
                      (encoding : (colors : Nat) → TileSet size colors → EncCNF (List EncCNF.Var))
                      : IO Unit := do
  plotData name ["sols"] size fun colors tiles => do
    let (blocking_vars, state) := EncCNF.new (encoding colors tiles)
    let count ← IO.mkRef 0
    
    SATSolve.allSols state (reportProgress := true) blocking_vars
      (perItem := fun _ => count.modify (·+1))
    
    return [toString <| ←count.get]


def plotSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "sign" size fun colors ts => do
    let tile_vars ← Constraints.colorCardConstraints ts.tiles colors 
    return tile_vars.map (·.2)

def plotEdgeSignSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgesign" size fun colors ts => do
    let tile_vars ← Constraints.colorCardConstraints ts.tiles colors 
    return tile_vars.filterMap (fun (t, v) =>
      if !t.isCenter then some v else none)

def plotPuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "puzzle" size fun _ ts => do
    match ← Constraints.puzzleConstraints ts with
    | .error s => panic! s!"it got sad :(\n{s}"
    | .ok tsv => 
      return tsv.diamondVarList

def plotEdgePuzzleSolCounts (size : Nat) : IO Unit := do
  plotSolCounts "edgepuzzle" size fun _ ts => do
    match ← Constraints.puzzleConstraints ts (onlyEdge := true) with
    | .error s => panic! s!"it got sad :(\n{s}"
    | .ok tsv => 
      return tsv.borderDiamondVarList

def plotCorr_sign_puzzle_withTimes (size : Nat) : IO Unit := do
  plotData "corr_sign_puzzle_timed" ["signsols","puzzlesols","soltime","soltime_withsigns"]
    size fun colors ts => do
      -- Count solutions to just polarity constraints
      let signsols ← (do
        let (blocking_vars, state) := EncCNF.new do
          let tile_vars ← Constraints.colorCardConstraints ts.tiles colors 
          return tile_vars.map (·.2)

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := fun _ => count.modify (·+1))
        
        return ← count.get)
      
      -- Count solutions to just puzzle constraints (and time it)
      let (soltime, puzzlesols) ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new do
          match ← Constraints.puzzleConstraints ts with
          | .error s => panic! s!"it got sad :(\n{s}"
          | .ok tsv => 
            return tsv.diamondVarList

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := fun _ => count.modify (·+1))
        
        return ← count.get)

      -- Count solutions to just puzzle constraints (and time it)
      let (soltime_withsigns, puzzlesols') ← IO.timeMs (do
        let (blocking_vars, state) := EncCNF.new do
          match ← Constraints.puzzleConstraints ts with
          | .error s => panic! s!"it got sad :(\n{s}"
          | .ok tsv => 
            return tsv.diamondVarList

        let count ← IO.mkRef 0

        SATSolve.allSols state (reportProgress := true) blocking_vars
          (perItem := fun _ => count.modify (·+1))
        
        return ← count.get)
      
      assert! (puzzlesols = puzzlesols')

      return [toString signsols, toString puzzlesols, toString soltime, toString soltime_withsigns]

def findEternityEdgeSols : IO Unit := do
  let e2 ← fetchEternity2Tiles
  match EncCNF.new do
    let _   ← Constraints.colorCardConstraints e2.tiles 17
    (Constraints.puzzleConstraints e2 (onlyEdge := true)).bind (m := EncCNF)
      (fun tsv => do
        Constraints.fixCorner tsv
        return tsv
      )
  with
  | (.error s, _) =>
    IO.println s!"Error building encoding: {s}"
  | (.ok tsv, state) =>
  let count ← IO.mkRef 0
  SATSolve.allSols state (reportProgress := true) tsv.borderDiamondVarList
    (perItem := fun assn => do
      let i ← count.modifyGet (fun ct => (ct, ct + 1))
      IO.FS.withFile s!"temp/border_sols/e2_border_sol_{i}.txt" .write (fun handle =>
        for var in tsv.borderDiamondVarList do
          for isTrue in assn.find? var do
            handle.putStrLn <| s!"{state.names.find! var} {isTrue}"
      )
    )




open Cli

def runGenTileSetCmd (p : Parsed) : IO UInt32 := do
  IO.println "c generated randomly"
  let size : Nat := p.flag! "size" |>.as! Nat
  let colors : Nat := p.flag! "colors" |>.as! Nat
  let bordercolors : Nat := p.flag! "bordercolors" |>.as! Nat

  let colors := if colors = 0 then size + 1 else colors
  let bordercolors := if bordercolors = 0 then size.sqrt + 1 else bordercolors

  let ts ← genTileSet size colors bordercolors
  IO.println ts.toFileFormat

  return 0


def genTileSetCmd := `[Cli|
  gen_tile_set VIA runGenTileSetCmd; ["0.0.1"]
  "Generate a random tile set."

  FLAGS:
    size : Nat; "The height/width of the board"
    colors : Nat; "The number of colors to fill the board with (0 means size+1)"
    bordercolors : Nat; "The number of colors to fill the border with (0 means sqrt(size) + 1)"

  EXTENSIONS:
    defaultValues! #[("colors", "0"), ("bordercolors", "0")]
]

def mainCmd := `[Cli|
  eternity2 NOOP; ["0.0.1"]
  "Tools working towards a solution to Eternity II"

  SUBCOMMANDS:
    genTileSetCmd
]

def main (args : List String) : IO UInt32 := do
  plotCorr_sign_puzzle_withTimes 6
  return 0

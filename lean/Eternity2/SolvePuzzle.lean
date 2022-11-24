import Eternity2.EdgeConstraints
import Eternity2.Board
import Eternity2.SATSolve

namespace Eternity2.SolvePuzzle

open Constraints EncCNF

def decodeDiamondBoard (tsv : Constraints.TileSetVariables size b c)
              (s : Std.HashMap EncCNF.Var Bool) :=
  let tb : DiamondBoard size (Option (Color.withBorder b c)) := {
    board :=
      Array.init _ (fun k =>
          List.fins _
            |>.find? (fun color => s.find? (tsv.diamond_vars (.ofFin k) color) |>.get!)
      )
    boardsize := by simp
  }
  tb

def decodeTileBoard
      (tsv : Constraints.TileSetVariables size b c)
      (s : Std.HashMap EncCNF.Var Bool)
    : Except String (TileBoard size (Color.withBorder b c)) := do
  let board ←
    Array.initM _ (fun i => do
      return ← Array.initM _ (fun j => do
        match
          List.fins _
            |>.find? (fun p => s.find? (tsv.piece_vars p ⟨i,j⟩ ) |>.get!)
            |>.map (fun p => tsv.tiles[tsv.h_ts.symm ▸ p]!)
        with
        | some t => return t
        | none => throw "Incomplete tile assignment"
      )
    )
  let tb : TileBoard size (Color.withBorder b c) := {
    board := board
    board_size := sorry
  }
  return tb


def writeSolution (filename : System.FilePath)
                  (tsv : TileSetVariables size b c)
                  (tileboard : TileBoard size (Color.withBorder b c))
                : IO Unit := do
  IO.FS.withFile filename .write (fun h =>
    -- h.putStrLn "c pieceNum x y rotation"
    h.putStrLn ""
  )
  for (i, tile) in tsv.tiles.enum do
    let mut found := false
    for y in [0, size] do
      for x in [0, size] do
        match Tile.numRotations tileboard.board[y]![x]! tile with
        | some rot =>
          found := true
          IO.FS.withFile filename .append (fun h =>
            h.putStrLn s!"{i} {x} {y} {rot}"
          )
          break
        | none => continue
      if found then break

def readSolution (filename : System.FilePath)
                 (tsv : TileSetVariables size b c)
               : IO (TileBoard size (Color.withBorder b c)) := do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  let data := contents.splitOn "\n" |>.filter (!·.startsWith "c")

  let parseLine := fun (line : String) =>
    match line.splitOn " " with
    | [t, x, y, r] => (
      match (t.toNat?, x.toNat?, y.toNat?, r.toNat?) with
      | (some t, some x, some y, some r) => (t,x,y,r)
      | _ => panic! s!"Could not parse integers on line: {line}"
    )
    | _ => panic! s!"Incorrectly formatted sol line: {line}"

  let mut temp_board :=
    Array.init size (fun y => Array.init size (fun x => none))
  for (t,x,y,r) in data.map parseLine do
    temp_board :=
      temp_board.set! y (temp_board[y]!.set! x (some <| tsv.tiles[t]!.rotln r))

  let board := Array.init size (fun y =>
    Array.init size (fun x =>
      match temp_board[y]![x]! with
      | some t => t
      | none => panic! "Incomplete solution loaded"
    )
  )

  let tb : TileBoard size (Color.withBorder b c) := {
    board := board
    board_size := by simp
  }
  return tb


def solve (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  : Option (DiamondBoard size (Option (Color.withBorder b c))) :=
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  SATSolve.solve enc (pVars ++ dVars)
  |>.map fun (_, assn) =>
  decodeDiamondBoard tsv assn

def solveAll (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  : IO (List (DiamondBoard size (Option (Color.withBorder b c)))) := do
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  let sols : IO.Ref (List _) ← IO.mkRef []
  SATSolve.allSols enc (pVars ++ dVars) (varsToBlock := dVars) (perItem := fun assn => do
    sols.modify (decodeDiamondBoard tsv assn :: ·)
  )
  return ←sols.get

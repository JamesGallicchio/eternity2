import Eternity2.Puzzle.EdgeConstraints
import Eternity2.Puzzle.Board
import Eternity2.SATSolve

namespace Eternity2.SolvePuzzle

open Constraints EncCNF

def decodeDiamonds (tsv : Constraints.TileSetVariables size b c)
              (s : Std.HashMap EncCNF.Var Bool) :=
  let tb : DiamondBoard size (Option (Color.withBorder b c)) := {
    board :=
      Array.init _ (fun k =>
          List.fins _
            |>.find? (fun color => s.find? (tsv.diamond_vars (.ofFin k) color) |>.getD false)
      )
    boardsize := by simp
  }
  tb

def decodePieces
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
                  (board : DiamondBoard size (Color.withBorder b c))
                : IO Unit := do
  IO.FS.withFile filename .write (fun h =>
    -- h.putStrLn "c pieceNum x y rotation"
    h.putStrLn ""
  )
  for (i, tile) in tsv.tiles.enum do
    let mut found := false
    for hx : x in [0:size] do
      for hy : y in [0:size] do
        let x : Fin size := ⟨x,hx.2⟩
        let y : Fin size := ⟨y,hy.2⟩
        match Tile.numRotations (board.diamond_to_tile x y) tile with
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
    Array.init size (fun _ => Array.init size (fun _ => none))
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
  |>.2.getAssn?.map fun assn =>
  decodeDiamonds tsv assn

/-- Find all solutions -/
def solveAll (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  (termCond : Option (IO Bool) := none)
  : IO (List (DiamondBoard size (Option (Color.withBorder b c)))) := do
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  let sols : IO.Ref (List _) ← IO.mkRef []
  SATSolve.allSols enc (pVars ++ dVars) (varsToBlock := dVars)
    (termCond := termCond)
    (perItem := fun assn => do
      sols.modify (decodeDiamonds tsv assn :: ·))
  return ←sols.get

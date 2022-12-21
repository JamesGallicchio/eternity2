import Eternity2.Puzzle.EdgeConstraints
import Eternity2.Puzzle.Board
import Eternity2.Puzzle.BoardSol
import Eternity2.Puzzle.SignSol
import Eternity2.SATSolve

namespace Eternity2

open Constraints EncCNF

def SolvePuzzle.decodeDiamonds (tsv : Constraints.TileSetVariables size b c)
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

def SolvePuzzle.decodePieces
      (tsv : Constraints.TileSetVariables size b c)
      (s : Std.HashMap EncCNF.Var Bool)
    : Except String (BoardSol tsv.ts) := do
  let board ← decodeDiamonds tsv s |>.expectFull
  let sol ←
    Array.initM _ (fun p => do
      match
        SquareIndex.all size
          |>.find? (fun idx => s.find? (tsv.piece_vars p idx) |>.get!)
      with
      | some idx =>
        let tile := tsv.ts.tiles[tsv.ts.h_ts.symm ▸ p]
        match Tile.numRotations (board.diamond_to_tile idx.row idx.col) tile with
        | some rot => return (idx,rot)
        | none => throw "tile {p} does not fit at {i},{j} in the diamond solution:\n{board}"
      | none => throw "Incomplete tile assignment"
    )
  have : sol.size = size * size := sorry
  return ⟨(sol[this.symm ▸ ·])⟩

def SolvePuzzle.solve (enc : EncCNF.State) (tsv : TileSetVariables size b c)
  : Option (DiamondBoard size (Option (Color.withBorder b c))) :=
  let pVars := tsv.pieceVarList
  let dVars := tsv.diamondVarList
  SATSolve.solve enc (pVars ++ dVars)
  |>.2.getAssn?.map fun assn =>
  decodeDiamonds tsv assn

/-- Find all solutions -/
def SolvePuzzle.solveAll (enc : EncCNF.State) (tsv : TileSetVariables size b c)
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

import Eternity2.Puzzle.BoardSol
import Eternity2.Puzzle.EdgeConstraints
import SolverConfig

namespace Eternity2.SolvePuzzle

open Constraints LeanSAT Encode EncCNF

structure EncodingSettings where
  useRedundant  : Bool := true
  usePolarity   : Bool := false
  fixCorner     : Bool := true
  fixCorners    : Option (Fin 6) := none

def encodePuzzle (ts : TileSet size (Tile <| Color.WithBorder s)) (es : EncodingSettings)
  : EncCNF (Constraints.TileSetVariables size s)
  := do
  let tsv ← Constraints.mkVars ts
  Constraints.compactEncoding tsv

  if es.useRedundant then
    Constraints.forbiddenColors tsv
    Constraints.pieceExplicitConstraints tsv

  if es.usePolarity then
    Constraints.colorCardConstraints tsv
    Constraints.associatePolarities tsv

  match es.fixCorners with
  | none => if es.fixCorner then Constraints.fixCorner tsv
  | some i => Constraints.fixCorners tsv i

  return tsv

def decodeToDiamondBoard (tsv : Constraints.TileSetVariables size s) (m : Assn) :=
  let tb : DiamondBoard size (Option (Color.WithBorder s)) := {
    board :=
      Array.init _ (fun k =>
          Color.allColors
            |>.find? (fun color => m.find? (tsv.diamond_vars (.ofFin k) color) |>.getD false)
      )
    boardsize := by simp
  }
  tb

def decodeSol
      (tsv : Constraints.TileSetVariables size s)
      (assn : LeanSAT.Assn)
    : Except String (BoardSol tsv.ts) := do
  let board ← decodeToDiamondBoard tsv assn |>.expectFull
  let sol ←
    Array.initM _ (fun p => do
      match
        SquareIndex.all size
          |>.find? (fun idx => assn.find? (tsv.piece_vars p idx) |>.get!)
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


def solve (enc : EncCNF.State) (tsv : TileSetVariables size s) :=
  show IO _ from do
  match ← Solver.solve enc.toFormula with
  | .sat assn =>
    return some <| decodeSol tsv assn
  | _ =>
    return none

/-- Find all solutions -/
def solveAll (enc : EncCNF.State) (tsv : TileSetVariables size s) :=
  show IO _ from do
  let dVars := tsv.diamondVarList
  let sols ← Solver.allSolutions enc.toFormula (varsToBlock := dVars)
  return ← sols.mapM (IO.ofExcept <| decodeSol tsv ·)

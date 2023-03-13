import Eternity2.Puzzle.BoardClues
import Eternity2.Puzzle.BoardSol
import Eternity2.Puzzle.Encoding

namespace Eternity2.SolvePuzzle

open Encoding LeanSAT Encode EncCNF

structure EncodingSettings where
  useRedundant  : Bool := true
  usePolarity   : Bool := false
  fixCorners    : Option (Fin 24) := none

def encodePuzzle (ts : TileSet size (Tile <| Color.WithBorder s)) (es : EncodingSettings)
  : EncCNF (TileSetVariables size s)
  := do
  let tsv ← mkVars ts
  compactEncoding tsv

  if es.useRedundant then
    forbiddenColors tsv
    pieceExplicitConstraints tsv

  if es.usePolarity then
    colorCardConstraints tsv
    associatePolarities tsv

  match es.fixCorners with
  | none => pure ()
  | some i => fixCorners tsv i

  return tsv



def encodeDiamondBoard (tsv : TileSetVariables size s) (board : DiamondBoard size (Color.WithBorder s))
  : Assn := Id.run do
  let mut assn : Assn := Std.HashMap.empty
  for i in List.fins _ do
    assn := assn.insert (tsv.diamond_vars (.ofFin i) board.board[board.boardsize.symm ▸ i]) true
  return assn

def decodeDiamondBoard (tsv : TileSetVariables size s) (m : Assn) :=
  let tb : DiamondBoard size (Option (Color.WithBorder s)) := {
    board :=
      Array.init _ (fun k =>
          Color.allColors
            |>.find? (fun color => m.find? (tsv.diamond_vars (.ofFin k) color) |>.getD false)
      )
    boardsize := by simp
  }
  tb

def encodeSol (tsv : TileSetVariables size s) (sol : BoardSol tsv.ts) : Except String LeanSAT.Assn := do
  return encodeDiamondBoard tsv <|
    (← DiamondBoard.expectFull <|
      .ofTileBoard (← sol.toTileBoard))

def decodeSol
      (tsv : TileSetVariables size s)
      (assn : LeanSAT.Assn)
    : Except String (BoardSol tsv.ts) := do
  let board ← decodeDiamondBoard tsv assn |>.expectFull
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

def encodeClues (tsv : TileSetVariables size s) (clues : BoardClues tsv.ts) : EncCNF Unit := do
  for (i,si,r) in clues.clues do
    addClause (tsv.piece_vars i si)
    have : i < tsv.ts.tiles.length := by cases i; rw [←tsv.ts.h_ts] at *; assumption
    let tile := tsv.ts.tiles[i].rotln r
    addClause (tsv.diamond_vars si.up tile.up)
    addClause (tsv.diamond_vars si.right tile.right)
    addClause (tsv.diamond_vars si.down tile.down)
    addClause (tsv.diamond_vars si.left tile.left)

def solve [Solver IO] (enc : EncCNF.State) (tsv : TileSetVariables size s) :=
  show IO _ from do
  match ← Solver.solve enc.toFormula with
  | .sat assn =>
    return some <| decodeSol tsv assn
  | _ =>
    return none

/-- Find all solutions -/
def solveAll [Solver IO] (enc : EncCNF.State) (tsv : TileSetVariables size s) :=
  show IO _ from do
  let dVars := tsv.diamondVarList
  let sols ← Solver.allSolutions enc.toFormula (varsToBlock := dVars)
  return ← sols.mapM (IO.ofExcept <| decodeSol tsv ·)

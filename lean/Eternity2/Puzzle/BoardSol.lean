import Eternity2.Puzzle.Board
import Eternity2.Puzzle.TileSet

namespace Eternity2

structure BoardSol [BEq c] (ts : TileSet size c) where
  /-- For each tile in tileset, its index + rotation (0 = up) -/
  pieceIdx : Fin (size * size) → SquareIndex size × Fin 4

namespace BoardSol

def toTileBoard {ts : TileSet size (Tile <| Color.WithBorder s)}
                          (sol : BoardSol ts)
    : Except String (TileBoard size (Color.WithBorder s)) := do
  let mut temp_board :=
    Array.init size (fun _ => Array.init size (fun _ => none))
  for t in List.fins _ do
    let ({row,col},r) := sol.pieceIdx t
    temp_board :=
      temp_board.set! row (temp_board[row]!.set! col (some <| ts.tiles[ts.h_ts.symm ▸ t].rotln r))

  let board ← Array.initM size (fun row =>
    Array.initM size (fun col =>
      match temp_board[row]![col]! with
      | some t => pure t
      | none => throw "Incomplete solution loaded"
    )
  )

  let tb : TileBoard size (Color.WithBorder s) := {
    board := board
    board_size := sorry
  }
  return tb

def ofTileBoard (tb : TileBoard size (Color.WithBorder s))
  : Σ ts : TileSet size (Tile <| Color.WithBorder s), BoardSol ts :=
  let withIdx : Array (SquareIndex size × Tile _) :=
    (Array.init size fun row => Array.init size fun col =>
      ({row,col},tb.board[tb.board_size.1.symm ▸ row][(tb.board_size.2 _ _).symm ▸ col])
    ).flatten
  have : withIdx.size = size*size := sorry
  ⟨ ⟨withIdx.map (·.2) |>.toList, sorry⟩
  , ⟨fun idx => (withIdx[this.symm ▸ idx].1, 0)⟩
  ⟩

/- Rotate the tiles randomly. Also mix up their order -/
def scramble {ts : TileSet size (Tile <| Color.WithBorder s)} (sol : BoardSol ts)
  : RandomM ((ts : TileSet size (Tile <| Color.WithBorder s)) × BoardSol ts) := do
  /- Rotate the pieces -/
  let rotated ← ts.tiles.enum'.mapM (fun (i, tile) => do
    let rot ← RandomM.randFin 4
    /- og index, rotation vs og, rotated tile -/ 
    return (ts.h_ts ▸ i, rot, tile.rotln rot))
  /- Randomly permute the corners/sides/centers -/
  let corners ← rotated.filter (·.2.2.isCorner) |> RandomM.randPerm
  let sides   ← rotated.filter (·.2.2.isSide)   |> RandomM.randPerm
  let centers ← rotated.filter (·.2.2.isCenter) |> RandomM.randPerm
  /- Recombine -/
  have all := corners.toArray ++ sides ++ centers
  have h_all : all.size = size * size := sorry
  /- Tileset -/
  let tiles := all.toList.map (·.2.2)
  have h_tiles : tiles.length = size * size := by simp [h_all]
  /- solution -/
  let sol := Array.init (size*size) (fun i =>
    let (old_i, rot, tile) := all[h_all.symm ▸ i]
    let (pos, old_rot) := sol.pieceIdx old_i
    (pos,(old_rot+4-rot)%4))
  return ⟨⟨tiles, h_tiles⟩, ⟨(sol[·])⟩⟩

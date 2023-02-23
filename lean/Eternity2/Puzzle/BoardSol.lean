import Eternity2.Puzzle.Board
import Eternity2.Puzzle.TileSet
import Eternity2.Puzzle.EdgeConstraints

namespace Eternity2

structure BoardSol [BEq c] (ts : TileSet size c) where
  /-- For each tile in tileset, its index + rotation (0 = up) -/
  pieceIdx : Fin (size * size) → SquareIndex size × Fin 4

namespace BoardSol

def toTileBoard {ts : TileSet size (Tile <| Color.WithBorder s)}
                          (sol : BoardSol ts)
    : IO (TileBoard size (Color.WithBorder s)) := do
  let mut temp_board :=
    Array.init size (fun _ => Array.init size (fun _ => none))
  for t in List.fins _ do
    let (⟨x,y⟩,r) := sol.pieceIdx t
    temp_board :=
      temp_board.set! y (temp_board[y]!.set! x (some <| ts.tiles[ts.h_ts.symm ▸ t].rotln r))

  let board := Array.init size (fun y =>
    Array.init size (fun x =>
      match temp_board[y]![x]! with
      | some t => t
      | none => panic! "Incomplete solution loaded"
    )
  )

  let tb : TileBoard size (Color.WithBorder s) := {
    board := board
    board_size := by simp
  }
  return tb

def ofTileBoard (tb : TileBoard size (Color.WithBorder s))
  : Σ ts : TileSet size (Tile <| Color.WithBorder s), BoardSol ts :=
  let withIdx : Array (SquareIndex size × Tile _) :=
    (Array.init size fun i => Array.init size fun j =>
      (⟨i,j⟩,tb.board[tb.board_size.1.symm ▸ i][(tb.board_size.2 _ _).symm ▸ j])
    ).flatten
  have : withIdx.size = size*size := sorry
  ⟨ ⟨withIdx.map (·.2) |>.toList, sorry⟩
  , ⟨fun idx => (withIdx[this.symm ▸ idx].1, 0)⟩
  ⟩

/- Randomly rotate the tiles, and mix up their order -/
def scramble {ts : TileSet size (Tile <| Color.WithBorder s)} (sol : BoardSol ts)
  : IO ((ts : TileSet size (Tile <| Color.WithBorder s)) × BoardSol ts) := do
  /- Rotate the pieces -/
  let rotated ← ts.tiles.enum'.mapM (fun (i, tile) => do
    let rot ← IO.rand 0 3
    let rot' : Fin 4 := ⟨rot, sorry⟩
    /- og index, rotation vs og, rotated tile -/ 
    return (ts.h_ts ▸ i, rot', tile.rotln rot'))
  /- Randomly permute the corners/sides/centers -/
  let corners ← rotated.filter (·.2.2.isCorner) |> IO.randPerm
  let sides   ← rotated.filter (·.2.2.isSide)   |> IO.randPerm
  let centers ← rotated.filter (·.2.2.isCenter) |> IO.randPerm
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
    (pos,rot+old_rot))
  return ⟨⟨tiles, h_tiles⟩, ⟨(sol[·])⟩⟩

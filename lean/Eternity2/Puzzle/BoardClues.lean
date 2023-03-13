import Eternity2.Puzzle.BoardSol

namespace Eternity2

structure BoardClues [BEq c] (ts : TileSet size c) where
  /-- A piece index, its board index, its board rotation (0 = up) -/
  clues : List (Fin (size * size) × SquareIndex size × Fin 4)

def BoardClues.fixCornerOfSol [BEq c] {ts : TileSet size c}
  (bs : BoardSol ts) : Except String (BoardClues ts)
  := do
  -- find piece at 0,0
  for i in List.fins (size * size) do
    have : 0 < size := Nat.pos_of_ne_zero (fun h => by simp [h] at i; exact i.elim0)
    if (bs.pieceIdx i).1 = ⟨⟨0,this⟩,⟨0,this⟩⟩ then
      return ⟨[(i, bs.pieceIdx i)]⟩
  throw "didn't find piece at 0,0"

import Eternity2.Puzzle.Board
import Eternity2.Puzzle.TileSet

namespace Eternity2

structure SignSol [BEq c] (ts : TileSet size c) where
  signAt : Fin (size * size) → Option Sign

namespace SignSol

def ofBoard [BEq c] (ts : TileSet size c) : SignSol ts :=
  ⟨fun idx =>
    let ⟨r,c⟩ := SquareIndex.ofFin idx
    if (r.val + c.val) % 2 == 0 then some .plus else some .minus⟩


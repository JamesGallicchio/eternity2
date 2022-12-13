import Eternity2.Puzzle.Board
import Eternity2.Puzzle.TileSet
import Eternity2.Puzzle.BoardSol

namespace Eternity2

structure SignSol [BEq c] (ts : TileSet size c) where
  signAt : Fin (size * size) → Option Sign

namespace SignSol

def ofSol [BEq c] (ts : TileSet size c) (sol : BoardSol ts) : SignSol ts :=
  ⟨fun idx =>
    let (⟨r,c⟩,_) := sol.pieceIdx idx
    if (r.val + c.val) % 2 == 0 then some .plus else some .minus⟩


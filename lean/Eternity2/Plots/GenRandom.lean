import Eternity2.Puzzle.Board
import Eternity2.Puzzle.BoardSol
import Eternity2.Puzzle.TileSet

namespace Eternity2.GenRandom

private def isLegal [BEq c] (dboard : DiamondBoard size (Option c)) : Bool :=
  dboard.tileBoard
  |>.tiles
  |> List.filter (fun t => t.hasColor none |> not)
  |> (fun tiles =>
        List.foldr (fun t (acc, legal) =>
          if not (legal) || (List.find? (fun t' => Tile.eq t t') acc |>.isSome)
          then (acc, false)
          else (t::acc, legal)
        ) ([], true) tiles
     )
  |> (fun (_, legal) => legal)

private def blankBoard (size : Nat) : DiamondBoard size (Option (Color.WithBorder s)) :=
  Id.run do
    let mut a := ⟨
      Array.init (2 * (size * size.succ)) fun _ => none
    , by simp⟩

    /- Set the frame -/
    for i in DiamondIndex.frame size do
      a := a.set i (some .frame)

    return a

/-- `size`x`size` board with colors assigned randomly. -/
def board (size : Nat) (s)
  : IO (DiamondBoard size (Color.WithBorder s)) := do
  attempt 1000
where
  attempt (attempts : Nat) : IO _ := do
    match attempts with
    | 0 =>
      throw <| IO.Error.timeExpired 0 "too many attempts taken to generate board"
    | attempts+1 =>

    let mut a := blankBoard size
    let mut indices := DiamondIndex.border size ++ DiamondIndex.center size

    while !indices.isEmpty do
      /- Pick random index from indices -/
      let i' ← randFin indices.length sorry
      let i := indices[i']
      indices := indices.removeNth i'

      let mut colors :=
        if i.isBorder then Color.borderColors
        else Color.centerColors

      /- Pick a color that doesn't violate uniqueness constraint -/
      while !colors.isEmpty do
        let c' ← randFin colors.length sorry
        let c := colors[c']
        colors := colors.removeNth c'

        let a' := a.set i (some c)
        if isLegal a' then
          a := a'
          break

      if colors.isEmpty then
        -- failed to find a color :(
        return ← attempt attempts
      else
        -- got the color :)
        continue

    /- Now all the diamonds should be some, so we map! -/
    let board ← a.board.mapM (fun
      | none => panic! "none found in generated board?"
      | some c => pure c)

    if h : board.size = _ then
      return ⟨board, h⟩
    else
      panic! "board size wrong?"

def tileSet (size : Nat) (settings)
  : IO (TileSet size (Tile <| Color.WithBorder settings)) := do
  let b ← board size settings
  let t := DiamondBoard.tileBoard b
  let ⟨ts,_⟩ ← (BoardSol.ofTileBoard t).2.scramble
  return ts

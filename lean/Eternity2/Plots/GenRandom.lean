import Eternity2.Plots.BoardSuite
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
  : RandomM (Except String <| DiamondBoard size (Color.WithBorder s)) := do
  let mut attempts := 0
  while attempts < 1000 do
    match ← attempt () with
    | .ok a => return .ok a
    | .error _ =>
      attempts := attempts + 1
  return .error s!"ran out of attempts when generating board of size {size}"
where
  attempt (_ : Unit) : ExceptT String RandomM
                        (DiamondBoard size (Color.WithBorder s)) := do
    let mut a := blankBoard size
    let mut indices := DiamondIndex.border size ++ DiamondIndex.center size

    while !indices.isEmpty do
      /- Pick random index from indices -/
      let i' ← RandomM.randFin indices.length sorry
      let i := indices[i']
      indices := indices.removeNth i'

      let mut colors :=
        if i.isBorder then Color.borderColors
        else Color.centerColors

      /- Pick a color that doesn't violate uniqueness constraint -/
      while !colors.isEmpty do
        let c' ← RandomM.randFin colors.length sorry
        let c := colors[c']
        colors := colors.removeNth c'

        let a' := a.set i (some c)
        if isLegal a' then
          a := a'
          break

      if colors.isEmpty then
        -- failed to find a color :(
        throw "failed to find color"
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
  : ExceptT String RandomM (TileSet size (Tile <| Color.WithBorder settings)) := do
  let b ← board size settings
  let t := DiamondBoard.tileBoard b
  let ⟨ts,_⟩ ← (BoardSol.ofTileBoard t).2.scramble
  return ts

def boardSuite (seed : Nat) (output : System.FilePath) : IO BoardSuite := do
  let mut boards := #[]
  for size in [4:17] do
    let output := output / s!"{size}"
    IO.FS.createDir output
    for colors in [size+1:size*3+10] do
      let output := output / s!"{colors}"
      IO.FS.createDir output
      for iter in [0:20] do
        -- using seed + parameters as start for rng, make a board
        -- this is deterministic for the same seed, even if the range of size/colors/iters changes
        let gen := mkStdGen <| (hash [seed, size, colors, iter]).toNat
        let colors :=
          let border := Nat.sqrt size + 1
          { border := List.range border
          , center := List.range colors |>.map (·+border) }
        let b ←
          GenRandom.board size colors
          |> RandomM.run gen
          |>.1 |> IO.ofExcept
        -- write the resulting puzzle + the default solution to files
        let t := b.tileBoard
        let ⟨ts,b⟩ ← (BoardSol.ofTileBoard t).2.scramble
        let dir := output / s!"board_{iter}"
        IO.FS.createDir dir
        FileFormat.TileSet.toFile  (dir / "puzzle.puz") ts
        FileFormat.BoardSol.toFile (dir / "default_sol.sol") b
        -- construct BoardDir
        let bd : BoardDir := {
          puzFile := dir / "puzzle.puz",
          size, colors, ts,
          sols := #[(dir / "default_sol.sol", b)]
          allSols := false
          }
        boards := boards.push bd
  return ⟨boards⟩

#eval show IO _ from do
  let db ← IO.ofExcept <| (← board 4 ⟨List.range 3, List.range 5⟩)
  let tb := db.tileBoard
  IO.println tb

  let ⟨ts,b⟩ ← (BoardSol.ofTileBoard tb).2.scramble

  IO.println ts
  IO.println <| FileFormat.TileSet.toFileFormat ts
  IO.println <| FileFormat.BoardSol.toFileFormat b

  let tb' ← IO.ofExcept b.toTileBoard

  IO.println tb'

import Eternity2.Puzzle.Board

namespace Eternity2

open Std

structure TileSet (size : Nat) (color : Type u) where
  tiles : List (Tile color)
deriving Inhabited, BEq

def TileBoard.tileSet (tb : TileBoard size c) : TileSet size c :=
  ⟨tb.tiles⟩

namespace TileSet

def toFileFormat (ts : TileSet size (Color.withBorder b c)) : String :=
  s!"c {size}x{size} board with {b} border colors, {c} center colors\n" ++
  s!"p tile {size} {size}\n" ++
  String.intercalate "\n"
    ( ts.tiles.map (fun {up, right, down, left} =>
        s!"{up} {right} {down} {left}")
    ) ++ "\n"


def toFile (filename : String) (ts : TileSet size (Color.withBorder b c)) : IO Unit := do
  IO.FS.withFile filename .write (fun handle =>
    handle.putStr (toFileFormat ts))

def fromFile (filename : String) : IO (Σ size b c, TileSet size (Color.withBorder b c)) := do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  match contents.splitOn "\n"
    |>.filter (!·.startsWith "c")
    |>.dropWhile (fun s => !s.startsWith "p")
  with
  | [] => panic! "No p line in file"
  | pline::rest =>
  let size :=
    match pline.splitOn " " with
    | ["p", "tile", w] => String.toNat! w
    | ["p", "tile", w, h] =>
      if w = h then String.toNat! w else panic! "Not a square (currently unsupported)"
    | ["p", "tile", w, h, _] =>
      if w = h then String.toNat! w else panic! "Not a square (currently unsupported)"
    | _ => panic! s!"Incorrectly formatted p line: {pline}"

  let tiles : List (Tile Nat)
    ← rest
    |>.filter (!·.all Char.isWhitespace)
    |>.mapM (fun s =>
      match s.splitOn " " |>.map String.toNat? with
      | [some up, some right, some down, some left] =>
        return { up, right, down, left }
      | _ =>
        panic! s!"Bad input line: \"{s}\"")
  
  let maxCenterColor := tiles.map (fun t =>
      t.colors.maximum?.getD 0
    )
    |>.maximum?.getD 0

  let b := tiles.map (fun t =>
      (if t.up    = 0 then [t.left, t.right] else []) ++
      (if t.right = 0 then [t.up  , t.down ] else []) ++
      (if t.down  = 0 then [t.left, t.right] else []) ++
      (if t.left  = 0 then [t.up  , t.down ] else [])
      |>.maximum?.getD 0
    )
    |>.maximum?.getD 0

  let c := maxCenterColor - b

  let cMap (i : Nat) : IO (Color.withBorder b c) :=
    if _ : i = 0 then
      return Color.frameColor
    else if _ : i ≤ b then
      return Color.borderColor ⟨i-1,
        Nat.lt_of_lt_of_le (Nat.pred_lt (by assumption)) (by assumption)⟩
    else if _ : i ≤ maxCenterColor then
      assert! i-b-1 < c
      return Color.centerColor ⟨i-b-1,
        by sorry⟩
    else
      panic! s!"Found color {i}, even though maxCenterColor={maxCenterColor}"

  let tiles ← tiles.mapM (fun t => do
    let t : Tile _ := { up := ← cMap t.up, right := ← cMap t.right, down := ← cMap t.down, left := ← cMap t.left }
    if t.validate then
      return t
    else
      panic! s!"Interpreting file as having {b} border colors, {c} center colors, found invalid piece:\n{t}"
  )
  return ⟨size, b, c, ⟨tiles⟩⟩

def toString (ts : TileSet size (Color.withBorder b c)) : String :=
  ts.tiles.map (·.toString)
  |>.map (·.splitOn "\n")
  |>.foldl (fun L1 L2 => List.zipWith (· ++ " " ++ ·) L1 L2) ["","",""]
  |> String.intercalate "\n"

instance : ToString (TileSet size (Color.withBorder b c)) := ⟨toString⟩

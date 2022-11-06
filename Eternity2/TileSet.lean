import Eternity2.Board

namespace Eternity2

open Std

structure TileSet where
  tiles : List Tile
  size : Nat
  colors : Nat
deriving Inhabited, DecidableEq

def TileBoard.tileSet (tb : TileBoard size) (colors : Nat) : TileSet :=
  ⟨tb.tiles, size, colors⟩

namespace TileSet

def toFile (filename : String) (ts : TileSet) : IO Unit := do
  let size := Nat.sqrt ts.tiles.length
  let numColors :=
    ts.tiles.foldl (fun acc ⟨a,b,c,d,_⟩ =>
        [a,b,c,d].foldl (fun acc x => if x ≠ borderColor then acc.insert x () else acc) acc
      ) (HashMap.empty)
    |>.size
  let contents :=
    s!"p tile {size} {size} {numColors}\n" ++
    String.intercalate "\n"
      ( ts.tiles.map (fun ⟨u,d,l,r,_⟩ =>
          s!"{u.get!} {r.get!} {d.get!} {l.get!}")
      ) ++ "\n"
  IO.FS.withFile filename .write (fun handle =>
    handle.putStr contents)

def fromFile (filename : String) : IO TileSet := do
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

  let tiles := rest
    |>.filter (!·.all Char.isWhitespace)
    |>.map (fun s =>
      match s.splitOn " " |>.map String.toNat? with
      | [some a, some b, some c, some d] => ⟨a,c,d,b,none⟩
      | _ => panic! s!"Bad input line {s}")

  return ⟨tiles,size, tiles.map (fun t =>
    t.colors.filterMap id) |>.join.maximum?.getD 0⟩

def toString (ts : TileSet) : String :=
  ts.tiles.map (·.toString)
  |>.map (·.splitOn "\n")
  |>.foldl (fun L1 L2 => List.zipWith (· ++ " " ++ ·) L1 L2) ["","",""]
  |> String.intercalate "\n"

instance : ToString TileSet := ⟨toString⟩

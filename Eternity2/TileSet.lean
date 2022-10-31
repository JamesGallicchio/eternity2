import Eternity2.Board

namespace Eternity2

open Std

def TileSet := List Tile
deriving Inhabited, DecidableEq, ToString

namespace TileSet

def toFile (filename : String) (ts : TileSet) : IO Unit := do
  let size := Nat.sqrt ts.length
  let numColors :=
    ts.foldl (fun acc ⟨a,b,c,d,_⟩ =>
        [a,b,c,d].foldl (fun acc x => if x ≠ 0 then acc.insert x () else acc) acc
      ) (HashMap.empty)
    |>.size
  let contents :=
    s!"p tile {size} {size} {numColors}\n" ++
    String.intercalate "\n" (ts.map (fun ⟨u,d,l,r,_⟩ => s!"{u} {r} {d} {l}")) ++
    "\n"
  IO.FS.withFile filename .write (fun handle =>
    handle.putStr contents)

def fromFile (filename : String) : IO TileSet := do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  return contents.splitOn "\n"
    |>.filter (!·.startsWith "c")
    |>.dropWhile (fun s => !s.startsWith "p")
    |>.drop 1
    |>.filter (!·.all Char.isWhitespace)
    |>.map (fun s =>
      match s.splitOn " " |>.map String.toNat? with
      | [some a, some b, some c, some d] => ⟨a,c,d,b,none⟩
      | _ => panic! s!"Bad input line {s}")

def toString (ts : TileSet) : String :=
  ts.map (·.toString)
  |>.map (·.splitOn "\n")
  |>.foldl (fun L1 L2 => List.zipWith (· ++ " " ++ ·) L1 L2) ["","",""]
  |> String.intercalate "\n"

instance : ToString TileSet := ⟨toString⟩

structure TypedTileSet where
  corner: TileSet
  border: TileSet
  center: TileSet

def TileSet.splitToTypes : TileSet → TypedTileSet :=
  List.foldr (fun t acc =>
    if t.isCorner
    then { acc with corner := t :: acc.corner }
    else if t.isBorder
    then { acc with border := t :: acc.border }
    else { acc with center := t :: acc.center }
  ) ⟨[], [], []⟩

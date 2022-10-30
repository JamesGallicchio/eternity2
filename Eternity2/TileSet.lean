import Eternity2.Board

namespace Eternity2

def TileSet := List Tile

def TileSet.fromFile (filename : String) : IO TileSet := do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  return contents.splitOn "\n"
    |>.filter (!·.startsWith "c")
    |>.dropWhile (fun s => !s.startsWith "p")
    |>.drop 1
    |>.map (fun s =>
      match s.splitOn " " |>.map String.toNat? with
      | [some a, some b, some c, some d] => ⟨a,b,c,d,none⟩
      | _ => panic! s!"Bad input line {s}")

import Eternity2.Board

namespace Eternity2

def TileSet := List Tile

def TileSet.toFile (filename : String) (ts : TileSet) : IO Unit := do
  let size := Nat. ts.length
  let contents :=
    s!"p tile 16 16\n" ++
    String.intercalate "\n" (ts.map (fun ⟨u,d,l,r,_⟩ => s!"{u} {r} {d} {l}"))
  IO.FS.withFile filename .write (fun handle =>
    handle.putStr contents)

def TileSet.fromFile (filename : String) : IO TileSet := do
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

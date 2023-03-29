import Eternity2.Puzzle.SignSol

namespace Eternity2.FileFormat.SignSol

def toFileFormat [BEq t] {ts : TileSet size t} (ssol : SignSol ts) : String :=
  Id.run do
    let mut res := ""
    for i in List.fins _ do
      for sign in ssol.signAt i do
        res := res ++ s!"{i} {sign}\n"
    return res

def toFile (filename : System.FilePath) [BEq t] {ts : TileSet size t} (sol : SignSol ts) : IO Unit :=
  IO.FS.withFile filename .write (·.putStr (toFileFormat sol))

def ofFileFormat (contents : String) [BEq t] (ts : TileSet size t) : Except String (SignSol ts) := do
  let lines :=
    contents.splitOn "\n"
    |>.map (·.trim) |>.filter (fun l => !(l.length = 0 || l.startsWith "c"))
  let signs ← lines.mapM parseLine
  let map ← signs.foldlM (fun acc (i,s) =>
    if acc.contains i then
      .error s!"Piece {i} listed twice in sign assignment"
    else
      .ok (acc.insert i s)
  ) Std.HashMap.empty
  return ⟨map.find?⟩
where parseLine : String → Except String (Fin (size * size) × Sign) := fun line => do
    match line.splitOn " " with
    | [t, sign] =>
      let t ← t.toNat?.expectSome fun () => ""
      let sign ← match sign with
        | "+" => .ok Sign.plus
        | "-" => .ok Sign.minus
        | _ => .error s!"Expected + or -, got `{sign}`"
      if h : t < size * size then
        return ⟨⟨t,h⟩,sign⟩
      else
        throw s!"Piece index out of range: {t}"
    | _ => throw s!"Expected <piece index> <sign>, got `{line}`"

def ofFile [BEq t] (ts : TileSet size t) (filename : System.FilePath) :=
  show IO _ from do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  return ← IO.ofExcept <| ofFileFormat contents ts

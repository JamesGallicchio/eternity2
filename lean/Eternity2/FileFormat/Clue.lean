import Eternity2.Puzzle.BoardClues

namespace Eternity2.FileFormat.BoardClues

def toFileFormat [BEq t] {ts : TileSet size t} (clues : BoardClues ts) : String :=
  Id.run do
    let mut res := ""
    for (i, {row,col}, rot) in clues.clues do
      res := res ++ s!"{i} {col} {row} {rot}\n"
    return res

def toFile (filename : System.FilePath) [BEq t] {ts : TileSet size t}
            (sol : BoardClues ts) : IO Unit :=
  IO.FS.withFile filename .write (·.putStr (toFileFormat sol))

def ofFileFormat (contents : String) [BEq t] (ts : TileSet size t)
            : Except String (BoardClues ts) := do
  let lines :=
    contents.splitOn "\n"
    |>.map (·.trim) |>.filter (fun l => !(l.length = 0 || l.startsWith "c"))
  return ⟨← lines.mapM parseLine⟩
where parseLine : String → Except String (Fin _ × SquareIndex _ × Fin 4) := fun line => do
    match line.splitOn " " with
    | [t, col, row, r] => (
      match (t.toNat?, col.toNat?, row.toNat?, r.toNat?) with
      | (some t, some col, some row, some r) =>
        if ht : t ≥ size*size then
          throw s!"Tile index out of range: {line}"
        else if hx : col ≥ size then
          throw s!"Col {col} out of range: {line}"
        else if hy : row ≥ size then
          throw s!"Row {row} out of range: {line}"
        else if hr : r ≥ 4 then
          throw s!"Rotation {r} out of range: {line}"
        else
        let col : Fin size := ⟨col, by simp at hx; exact hx⟩
        let row : Fin size := ⟨row, by simp at hy; exact hy⟩
        return (
          ⟨t, by simp at ht; exact ht⟩,
          {row,col},
          ⟨r, by simp at hr; exact hr⟩)
      | _ => throw s!"Could not parse integers on line: {line}"
    )
    | _ => throw s!"Incorrectly formatted sol line: {line}"

def ofFile [BEq t] (ts : TileSet size t) (filename : System.FilePath) :=
  show IO _ from do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  return ← IO.ofExcept <| ofFileFormat contents ts

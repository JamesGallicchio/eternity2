import Eternity2.Puzzle.BoardSol

namespace Eternity2.FileFormat.BoardSol

def toFileFormat [BEq c] {ts : TileSet size c} (sol : BoardSol ts) : String :=
  Id.run do
    let mut res := ""
    for i in List.fins _ do
      let ({row,col},rot) := sol.pieceIdx i
      res := res ++ s!"{i} {col} {row} {rot}\n"
    return res

def toFile (filename : System.FilePath)
    [BEq c] {ts : TileSet size c} (sol : BoardSol ts)
                : IO Unit :=
  IO.FS.withFile filename .write (·.putStr (toFileFormat sol))

def ofFileFormat (contents : String)
                 (ts : TileSet size (Tile <| Color.WithBorder s))
               : Except String (BoardSol ts) := do
  let data ← do
    let lines :=
      contents.splitOn "\n"
      |>.map (·.trim) |>.filter (fun l => !(l.length = 0 || l.startsWith "c"))
    let parsed ← lines.mapM parseLine 
    pure <| parsed.foldl (init := Std.HashMap.empty) (fun map (t,loc) => map.insert t loc)

  let array ← Array.initM (size*size) (fun i => do
      match data.find? i with
      | none => throw s!"Piece {i} is missing from solution"
      | some (col,row,r) => pure ({row,col},r))
  have : array.size = size*size := sorry
  return ⟨(array[this.symm ▸ ·])⟩

where parseLine : String → Except String (Fin _ × Fin _ × Fin _ × Fin 4) := fun line => do
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
        return (
          ⟨t,Nat.not_ge_eq _ _ ▸ ht⟩,
          ⟨col,Nat.not_ge_eq _ _ ▸ hx⟩,
          ⟨row,Nat.not_ge_eq _ _ ▸ hy⟩,
          ⟨r, by rw [Nat.not_ge_eq] at hr; exact hr⟩)
      | _ => throw s!"Could not parse integers on line: {line}"
    )
    | _ => throw s!"Incorrectly formatted sol line: {line}"

def ofFile (ts : TileSet size (Tile <| Color.WithBorder s)) (filename : System.FilePath) :=
  show IO _ from do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )
  return ← IO.ofExcept <| ofFileFormat contents ts

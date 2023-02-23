import Eternity2.Puzzle.BoardSol

namespace Eternity2.FileFormat.BoardSol

def toFile (filename : System.FilePath)
    [BEq c] {ts : TileSet size c} (sol : BoardSol ts)
                : IO Unit := do
  IO.FS.withFile filename .write (fun h => do
    h.putStrLn "c pieceNum x y rotation"
    h.putStrLn ""
    for i in List.fins _ do
      let (⟨x,y⟩,rot) := sol.pieceIdx i
      h.putStrLn s!"{i} {x} {y} {rot}"
  )

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
      | some (x,y,r) => pure (⟨x,y⟩,r))
  have : array.size = size*size := sorry
  return ⟨(array[this.symm ▸ ·])⟩

where parseLine : String → Except String (Fin _ × Fin _ × Fin _ × Fin 4) := fun line => do
    match line.splitOn " " with
    | [t, x, y, r] => (
      match (t.toNat?, x.toNat?, y.toNat?, r.toNat?) with
      | (some t, some x, some y, some r) =>
        if ht : t ≥ size*size then
          throw s!"Tile index out of range: {line}"
        else if hx : x ≥ size then
          throw s!"Row {x} out of range: {line}"
        else if hy : y ≥ size then
          throw s!"Col {y} out of range: {line}"
        else if hr : r ≥ 4 then
          throw s!"Rotation {r} out of range: {line}"
        else
        return (
          ⟨t,Nat.not_ge_eq _ _ ▸ ht⟩,
          ⟨x,Nat.not_ge_eq _ _ ▸ hx⟩,
          ⟨y,Nat.not_ge_eq _ _ ▸ hy⟩,
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

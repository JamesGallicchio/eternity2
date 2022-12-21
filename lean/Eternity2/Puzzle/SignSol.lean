import Eternity2.Puzzle.Board
import Eternity2.Puzzle.TileSet
import Eternity2.Puzzle.BoardSol

namespace Eternity2

structure SignSol [BEq c] (ts : TileSet size c) where
  signAt : Fin (size * size) → Option Sign

namespace SignSol

def ofSol [BEq c] (ts : TileSet size c) (sol : BoardSol ts) : SignSol ts :=
  ⟨fun idx =>
    let (⟨r,c⟩,_) := sol.pieceIdx idx
    if (r.val + c.val) % 2 == 0 then some .plus else some .minus⟩

def writeSolution (filename : System.FilePath)
    [BEq c] {ts : TileSet size c} (sol : SignSol ts)
                : IO Unit := do
  IO.FS.withFile filename .write (fun h => do
    h.putStrLn "c pieceNum sign"
    h.putStrLn ""
    for i in List.fins _ do
      match sol.signAt i with
      | none => pure ()
      | some b =>
        h.putStrLn s!"{i} {b}"
  )

def readSolution (filename : System.FilePath)
                 (ts : TileSet size (Color.withBorder b c))
               : IO (SignSol ts) := do
  let contents ← IO.FS.withFile filename .read (fun handle =>
    handle.readToEnd
  )

  have parseLine : String → IO (Fin _ × Sign) := fun line => do
    match line.splitOn " " with
    | [t, sign] => (
      match (t.toNat?, Sign.ofString sign) with
      | (some t, some s) =>
        if ht : t ≥ size*size then
          panic! s!"Tile index out of range: {line}"
        else
          pure (⟨t,by rw [Nat.not_ge_eq] at ht; exact ht⟩, s)
      | _ => panic! s!"Could not parse line: {line}"
    )
    | _ => panic! s!"Incorrectly formatted sol line: {line}"

  let data ← do
    let lines :=
      contents.splitOn "\n"
      |>.map (·.trim) |>.filter (fun l => !(l.length = 0 || l.startsWith "c"))
    let parsed ← lines.mapM parseLine 
    pure <| parsed.foldl (init := Std.HashMap.empty) (fun map (t,s) => map.insert t s)

  let array := Array.init (size*size) (data.find?)
  have : array.size = size*size := by simp
  return ⟨(array[this.symm ▸ ·])⟩


import Eternity2.Puzzle.TileSet

namespace Eternity2.FileFormat.TileSet

def toFileFormat.color (c : Color.WithBorder s) : String :=
  match c with
  | .frame => "0"
  | .border n _ | .center n _ => toString n

def toFileFormat.tile (t : Tile (Color.WithBorder s)) : String :=
  s!"{color t.up} {color t.right} {color t.down} {color t.left}{
      match t.sign with
      | none => ""
      | some .plus => " +"
      | some .minus => " -"
    }"

def toFileFormat (ts : TileSet size (Tile (Color.WithBorder s))) :=
  s!"{size} {size}\n" ++
  String.intercalate "\n"
    ( ts.tiles.map toFileFormat.tile ) ++ "\n"

def toFile (filename : System.FilePath) (ts : TileSet size (Tile <| Color.WithBorder s))
                : IO Unit := do
  IO.FS.withFile filename .write (fun h => h.putStr (toFileFormat ts))


def ofFileFormat (s : String) :
  Except String (Σ size s, TileSet size (Tile (Color.WithBorder s)))
  := do
  match s.splitOn "\n"
    |>.filter (fun line => !line.startsWith "c" && !line.isEmpty)
  with
  | [] => throw "No board size line in file"
  | sline::rest =>
  let size ←
    match sline.splitOn " " with
    | [w] => pure <| String.toNat! w
    | [w, h] =>
      if w = h then
        pure <| String.toNat! w
      else throw "Not a square (currently unsupported)"
    | _ => throw s!"Expected board size line `<cols> [rows]`, but got: {sline}"

  let tiles : List (Tile Nat) ←
    rest
    |>.filter (!·.all Char.isWhitespace)
    |>.mapM (fun s => do
      match s.splitOn " " with
      | up :: right :: down :: left :: rest =>
        let parse := (fun s => s.toNat? |>.expectSome fun () => s!"expected nat, got {s}")
        let (up, right, down, left) :=
          (← parse up, ← parse right, ← parse down, ← parse left)
        return { up, right, down, left, sign := ← (do match rest with
          | ["+"] => return some .plus
          | ["-"] => return some .minus
          | []    => return none
          | _ => throw s!"Expected end-of-line, got {String.intercalate " " rest}"
          )}
      | _ =>
        throw s!"Bad input line: \"{s}\"")
  
  if tiles.all (·.colors.all (· > 0)) then
    throw "Appears to be an unframed puzzle; these are not yet supported."

  let (borderColors, centerColors) ←
    tiles.foldlM (fun (bc,cc) y => do
      match y.classifyGen 0 with
      | none => throw s!"Piece has an invalid shape: {y}"
      | some ⟨_, .corner x y _⟩ => return (x::y::bc, cc)
      | some ⟨_, .side x y z _⟩ => return (x::z::bc, y::cc)
      | some ⟨_, .center w x y z _⟩ => return (bc, w::x::y::z::cc))
    ([],[])

  let borderColors := borderColors.distinct
  let centerColors := centerColors.distinct

  let s : Color.WithBorder.Settings := ⟨borderColors,centerColors⟩

  let tileMap (t : Tile Nat) : Except String (Tile (Color.WithBorder s)) := do
    match t.classifyGen 0 with
    | none => throw "misclassified even though should have errored earlier? 5467654"
    | some ⟨n, .corner x y _⟩ =>
      return {  up   := .border x sorry , right := .border y sorry
             ,  down := .frame          , left  := .frame         , sign := t.sign }
    | some ⟨n, .side x y z _⟩ =>
      return {  up   := .border x sorry , right := .center y sorry
             ,  down := .border z sorry , left  := .frame         , sign := t.sign }
    | some ⟨n, .center w x y z _⟩ =>
      return {  up   := .center w sorry , right := .center x sorry
             ,  down := .center y sorry , left  := .center z sorry, sign := t.sign }


  let tiles ← tiles.mapM (tileMap)
  if h : tiles.length = size * size then
    return ⟨size, s, tiles, h⟩
  else
    throw s!"File lists {tiles.length} pieces, but {size*size} were expected"


def ofFile (f : System.FilePath) := IO.FS.withFile f .read (·.readToEnd) >>= IO.ofExcept ∘ ofFileFormat

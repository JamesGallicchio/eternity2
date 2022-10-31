import Eternity2.AuxDefs

namespace Eternity2

@[reducible]
def Color := Nat
def borderColor : Color := 0

inductive Sign
| plus  : Sign
| minus : Sign
deriving DecidableEq, Repr
def Sign.toString : Sign → String
| plus => "+"
| minus => "-"
instance : ToString Sign := ⟨Sign.toString⟩

structure Tile where
  (up down left right : Color)
  sign : Option Sign
deriving DecidableEq, Repr, Inhabited

namespace Tile

def toString (tile : Tile) :=
  let signage :=
    match tile.sign with
      | none => " "
      | some s => Sign.toString s
  s!"┌{tile.up}┐\n{tile.left}{signage}{tile.right}\n└{tile.down}┘"


instance: ToString Tile where
  toString := toString

def rotl : Tile → Tile
| ⟨up,down,left,right,sign⟩ => ⟨right,left,up,down,sign⟩

def eq (tile1 tile2 : Tile) :=
  rotate 0 || rotate 1 || rotate 2 || rotate 3
where rotate n := Function.iterate rotl n tile1 == tile2

def isCorner (tile : Tile) : Bool :=
  ( tile.up == borderColor
    && (tile.left == borderColor || tile.right == borderColor)) ||
  ( tile.down == borderColor
    && (tile.left == borderColor || tile.right == borderColor)
  )

def isBorder (tile : Tile) : Bool :=
  !(isCorner tile) &&
  ( tile.up == borderColor
  || tile.down == borderColor
  || tile.right == borderColor
  || tile.left == borderColor
  )

def isCenter (tile : Tile) : Bool :=
  !(isBorder tile) && !(isCorner tile)

end Tile


@[reducible]
def Diamond := {c : Color // c ≠ borderColor}
deriving Repr

instance : Inhabited Diamond where
  default := ⟨1, by decide⟩

structure TileBoard (size : Nat) where
  board : Array (Array Tile)
  board_size :
    board.size = size ∧ ∀ i, (h : i < board.size) → board[i].size = size

namespace TileBoard

instance : ToString (TileBoard size) where
  toString (tile : TileBoard size) :=
    tile.board.toList.map (·.toList.map (toString))
    |> List.map (fun row =>
        row
        |>.map (·.splitOn "\n")
        |>.foldl (fun L1 L2 => List.zipWith (· ++ " " ++ ·) L1 L2) ["","",""]
        |> String.intercalate "\n"
      )
    |> String.intercalate "\n"

def tileSet (tb : TileBoard size) : List Tile :=
  tb.board.foldr (·.toList ++ ·) []

end TileBoard

structure DiamondBoard (size : Nat) where
  board: Array (Array Diamond)
  boardsize: board.size = 2 * size - 1
  rowsize: ∀ i, (h : i < board.size) →
    if i % 2 = 0
    then board[i].size = size - 1
    else board[i].size = size

namespace DiamondBoard

def up_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if row.val = 0 then borderColor else
    dboard.board[2 * row.val - 1]![col]!
def down_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if row.val = size - 1 then borderColor else
    dboard.board[2 * row.val + 1]![col]!
def left_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if col.val = 0 then borderColor else
    dboard.board[2 * row.val]![col.val - 1]!
def right_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if col.val = size - 1 then borderColor else
    dboard.board[2 * row.val]![col]!

def diamond_to_tile (dboard : DiamondBoard size) (row col : Fin size) :=
  Tile.mk
    (up_color dboard row col)
    (down_color dboard row col)
    (left_color dboard row col)
    (right_color dboard row col)

def tileBoard (dboard : DiamondBoard size) (checker : Bool) : TileBoard size := Id.run do
  let mut a := Array.mkEmpty size
  for i in [0:size] do
    a := a.push (Array.mkEmpty size)
    for j in [0:size] do
      a := a.set! i
        <| (a.get! i).push
          <| diamond_to_tile dboard ⟨i, sorry⟩ ⟨j, sorry⟩
                (if checker then
                  some (if (i+j) % 2 = 0 then .plus else .minus)
                else none)
  return TileBoard.mk a sorry

/-- `size`x`size` board with `colors` colors assigned randomly. -/
def generate (size : Nat) (colors : Nat) : IO (DiamondBoard size) := do
  let mut a := Array.mkEmpty (2 * size - 1)
  for i in [0:2*size - 1] do
    let len := if i % 2 = 0 then (size - 1) else size
    a := a.push (Array.mkEmpty len)
    for j in [0:len] do
      let color ← IO.rand (borderColor + 1) colors
      a := a.set! i <| (a.get! i).push (⟨color, sorry⟩ : Diamond)
  return DiamondBoard.mk a sorry sorry

end DiamondBoard

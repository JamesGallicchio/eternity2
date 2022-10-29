import Eternity2.AuxDefs

namespace Tile

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
instance: ToString Sign := ⟨Sign.toString⟩

structure Tile where
  up: Color
  down: Color
  left: Color
  right: Color
  sign: Option Sign
deriving DecidableEq, Repr
instance: ToString Tile where
  toString tile := s!"\n {tile.up} \n{tile.left}{tile.sign}{tile.right}\n {tile.down} "

def rotl (tile : Tile) :=
  Tile.mk tile.right tile.left tile.up tile.down tile.sign

def eq (tile1 tile2 : Tile) :=
  rotate 0 || rotate 1 || rotate 2 || rotate 3
where rotate n := Function.iterate rotl n tile1 == tile2

@[reducible]
def Diamond := {c : Color // c ≠ borderColor}
deriving Repr
instance: Inhabited Diamond where
  default := ⟨1, by decide⟩

structure TileBoard (size : Nat) where
  board: Array (Array Tile)
  boardsize:
    board.size = size /\ ∀ i, (h : i < board.size) → board[i].size = size
instance: ToString (TileBoard size) where
  toString (tile : TileBoard size) :=
    toString (tile.board)

structure DiamondBoard (size : Nat) where
  board: Array (Array Diamond)
  boardsize: board.size = 2 * size - 1
  rowsize: ∀ i, (h : i < board.size) →
    if i % 2 = 0
    then board[i].size = size - 1
    else board[i].size = size
deriving Repr


def up_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if row.val = 0 then borderColor else
    dboard.board[2 * row.val - 1]![col]!
def down_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if row.val = 2 * row.val - 2 then borderColor else
    dboard.board[2 * row.val + 1]![col]!
def left_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if col.val = 0 then borderColor else
    dboard.board[2 * row.val]![col - 1]!
def right_color (dboard : DiamondBoard size) (row : Fin size) (col : Fin size) :=
  if col.val = size - 1 then borderColor else
    dboard.board[2 * row.val]![col]!

def diamond_to_tile (dboard : DiamondBoard size) (row col : Fin size) :=
  Tile.mk
    (up_color dboard row col)
    (down_color dboard row col)
    (left_color dboard row col)
    (right_color dboard row col)

def dboard_to_tboard (dboard : DiamondBoard size) : TileBoard size := Id.run do
  let mut a := Array.mkEmpty size
  for i in [0:size] do
    a := a.push (Array.mkEmpty size)
    for j in [0:size] do
      a := a.set! i
        <| (a.get! i).push <| diamond_to_tile dboard ⟨i, sorry⟩ ⟨j, sorry⟩ none
  return TileBoard.mk a sorry

def gen_dboard (size : Nat) (colors : Nat) : IO (DiamondBoard size) := do
  let mut a := Array.mkEmpty (2 * size - 1)
  for i in [0:2*size - 1] do
    let len := if i % 2 = 0 then (size - 1) else size
    a := a.push (Array.mkEmpty len)
    for j in [0:len] do
      let color ← IO.rand (borderColor + 1) colors
      a := a.set! i <| (a.get! i).push (⟨color, sorry⟩ : Diamond)
  return DiamondBoard.mk a sorry sorry


def Main : IO Unit := do
  let b ← gen_dboard 6 9
  let t := dboard_to_tboard b
  IO.print t

#eval Main

import Eternity2.AuxDefs

namespace Eternity2

@[reducible]
def Color := Option Nat
def Color.toString : Color → String
| none => "X"
| some c => s!"{c}"

def borderColor : Color := some 0

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
  s!"┌{tile.up.toString}┐\n{tile.left.toString}{signage}{tile.right.toString}\n└{tile.down.toString}┘"


instance: ToString Tile where
  toString := toString

def rotl : Tile → Tile
| ⟨up,down,left,right,sign⟩ => ⟨right,left,up,down,sign⟩

def eq (tile1 tile2 : Tile) :=
  rotate 0 || rotate 1 || rotate 2 || rotate 3
where rotate n := Function.iterate rotl n tile1 == tile2

def hasColor (tile : Tile) (color : Color) : Bool :=
     tile.up   == color || tile.down  == color
  || tile.left == color || tile.right == color

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

def colors : Tile → List Color
| ⟨up, down, left, right,_⟩ =>
  [up,down,left,right]

def getBorderColors (tile : Tile) : List Color :=
  if tile.isCenter then []
  else if tile.isBorder then
    if tile.up == borderColor || tile.down == borderColor
    then [tile.left, tile.right]
    else [tile.up, tile.down]
  else if tile.up == borderColor then
    [tile.down, if tile.left == borderColor then tile.right else tile.left]
  else [tile.up, if tile.left == borderColor then tile.right else tile.left]

def getCenterColors (tile : Tile) : List Color :=
  if tile.isCenter then [tile.up, tile.down, tile.left, tile.right]
  else if tile.isCorner then []
  else if tile.up   == borderColor then [tile.down]
  else if tile.down == borderColor then [tile.up]
  else if tile.left == borderColor then [tile.right]
  else [tile.left]

end Tile


@[reducible]
def Diamond := {c : Color // c ≠ borderColor}
deriving Repr

instance : Inhabited Diamond where
  default := ⟨some 1, by decide⟩

structure TileBoard (size : Nat) where
  board : Array (Array Tile)
  board_size :
    board.size = size ∧ ∀ i, (h : i < board.size) → board[i].size = size
  isFinalized: Bool
  finalize: isFinalized →
    ∀ i, (h : i < board.size) → ∀ j, (h' : j < board[i].size) →
      not (board[i][j].hasColor none)

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

def tiles (tb : TileBoard size) : List Tile :=
  tb.board.foldr (·.toList ++ ·) []

end TileBoard

structure DiamondBoard (size : Nat) where
  board: Array (Array Diamond)
  boardsize: board.size = 2 * size - 1
  rowsize: ∀ i, (h : i < board.size) →
    if i % 2 = 0
    then board[i].size = size - 1
    else board[i].size = size
  isFinalized: Bool
  finalize: isFinalized →
    ∀ i, (h : i < board.size) → ∀ j, (h' : j < board[i].size) →
      board[i][j].val != none

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
  return TileBoard.mk a sorry dboard.isFinalized sorry

def isLegal (dboard : DiamondBoard size) : Bool :=
  tileBoard dboard false
  |>.tiles
  |> List.filter (fun t => t.hasColor none |> not)
  |> (fun tiles =>
        List.foldr (fun t (acc, legal) =>
          if not (legal) || (List.find? (fun t' => Tile.eq t t') acc |>.isSome)
          then (acc, false)
          else (t::acc, legal)
        ) ([], true) tiles
     )
  |> (fun (_, legal) => legal)

def hasUnColored (board : Array (Array Diamond)) : Bool :=
  board.any (fun row => row.any (fun c => c.val.isNone))

/-- `size`x`size` board with `colors` colors assigned randomly. -/
def generate (size : Nat) (coreColors : Nat) (edgeColors : Nat) : IO (DiamondBoard size) := do
  let mut a := Array.mkEmpty (2 * size - 1)
  for i in [0:2*size - 1] do
    let len := if i % 2 = 0 then (size - 1) else size
    a := a.push (Array.mkEmpty len)
    for j in [0:len] do
      a := a.set! i <| (a.get! i).push (⟨none, sorry⟩ : Diamond)

  while hasUnColored a do
    let i ← IO.rand 0 (a.size - 1)
    let j ← IO.rand 0 (a[i]!.size - 1)

    if a[i]![j]!.val.isSome
    then continue

    let mut pickColor := true
    while pickColor do
      let c ← IO.rand (borderColor.get! + 1) <|
        if i == 0 || i == (a.size - 1) || j == 0 || j == (a[i]!.size - 1)
        then edgeColors
        else coreColors
      a := a.set! i <| (a.get! i).set! j (⟨some c, sorry⟩ : Diamond)
      let dboard : DiamondBoard size := DiamondBoard.mk a sorry sorry false sorry
      pickColor := not (isLegal dboard)

  return DiamondBoard.mk a sorry sorry true sorry

end DiamondBoard

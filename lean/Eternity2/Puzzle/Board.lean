import Eternity2.AuxDefs

namespace Eternity2

structure SquareIndex (size : Nat) where
  row : Fin size
  col : Fin size
deriving Repr, DecidableEq

inductive DiamondIndex (size : Nat) where
/-- col refers to the right triangle's column -/
| horz (row : Fin size) (col : Fin size.succ)
/-- row refers to the bottom triangle's row -/
| vert (row : Fin size.succ) (col : Fin size)
deriving Repr

namespace SquareIndex

def toFin : SquareIndex size → Fin (size * size)
| ⟨⟨i,hi⟩,⟨j,hj⟩⟩ => ⟨i * size + j, by
  cases size; case zero => contradiction
  case succ ps =>
  apply Nat.lt_of_succ_le
  rw [←Nat.add_succ]
  conv => rhs; rw [Nat.succ_mul]
  apply Nat.add_le_add
  apply Nat.mul_le_mul_right
  apply Nat.le_of_succ_le_succ hi
  exact hj⟩

private def maxIdx {psize : Nat} : Fin psize.succ := ⟨psize, Nat.lt_succ_self _⟩

private def middleFins (psize : Nat) : List (Fin psize.succ) :=
  forIn' (m := Id) [1:psize] [] (fun x h y =>
    .yield (⟨x, by exact Nat.le_step h.2⟩ :: y))

def up : (i j : Fin size) → DiamondIndex size
| i, j => .vert ⟨i, Nat.le_step i.isLt⟩ j

def left : (i j : Fin size) → DiamondIndex size
| i, j => .horz i ⟨j, Nat.le_step j.isLt⟩

def down : (i j : Fin size) → DiamondIndex size
| i, j => .vert ⟨i+1, Nat.succ_le_succ i.isLt⟩ j

def right : (i j : Fin size) → DiamondIndex size
| i, j => .horz i ⟨j+1, Nat.succ_le_succ j.isLt⟩


def corners (size : Nat) : List (SquareIndex size × (Fin 2 → DiamondIndex size)) :=
  match size with
  | 0 => [] | _ + 1 =>
    [ ( ⟨0, 0⟩, fun
          | 0 => right  0 0
          | 1 => down   0 0)
    , ( ⟨0, maxIdx⟩, fun
          | 0 => down   0 maxIdx
          | 1 => left   0 maxIdx)
    , ( ⟨maxIdx, maxIdx⟩, fun
          | 0 => left   maxIdx maxIdx
          | 1 => up     maxIdx maxIdx)
    , ( ⟨maxIdx, 0⟩, fun
          | 0 => up     maxIdx 0
          | 1 => right  maxIdx 0)
    ]

def sides (size : Nat) : List (SquareIndex size × (Fin 3 → DiamondIndex size)) :=
  match size with
  | 0 => [] | psize + 1 =>
  middleFins psize |>.bind fun i =>
    [ ( ⟨0, i⟩, fun
        | 0 => right  0 i
        | 1 => down   0 i
        | 2 => left   0 i )
    , ( ⟨i, 0⟩, fun
        | 0 => up     i 0
        | 1 => right  i 0
        | 2 => down   i 0 )
    , ( ⟨maxIdx, i⟩, fun
        | 0 => left   maxIdx i
        | 1 => up     maxIdx i
        | 2 => right  maxIdx i )
    , ( ⟨i, maxIdx⟩, fun
        | 0 => down   i maxIdx
        | 1 => left   i maxIdx
        | 2 => up     i maxIdx )
    ]

def center (size : Nat) : List (SquareIndex size × (Fin 4 → DiamondIndex size)) :=
  match size with
  | 0 => [] | psize + 1 =>
  middleFins psize |>.bind fun x =>
    middleFins psize |>.map fun y =>
      (⟨x,y⟩, fun
        | 0 => up     x y
        | 1 => right  x y
        | 2 => down   x y
        | 3 => left   x y)

def all (size : Nat) : List (SquareIndex size) :=
  List.fins size |>.bind fun i =>
    List.fins size |>.map fun j =>
      ⟨i,j⟩

instance : ToString (SquareIndex size) where
  toString | ⟨i, j⟩ => s!"r{i}c{j}"

end SquareIndex


namespace DiamondIndex

/-
 0 1 2
3 4 5 6
 7 8 9
a b c d
 e f g
h i j k
 l m n 
-/

def toFin : DiamondIndex size → Fin (2 * (size * size.succ))
| vert ⟨i,hi⟩ ⟨j,hj⟩ => ⟨i * (size + size.succ) + j, by
  simp [Nat.succ_mul, Nat.mul_add]
  apply Nat.lt_of_lt_of_le
  . apply Nat.lt_of_succ_le
    rw [←Nat.add_succ]
    apply Nat.add_le_add_left hj
  rw [Nat.add_comm, ←Nat.add_assoc]
  apply Nat.add_le_add
  . rw [Nat.add_comm, ←Nat.succ_mul, Nat.mul_comm]
    apply Nat.mul_le_mul_left _ hi
  . apply Nat.mul_le_mul_right
    apply Nat.le_of_succ_le_succ hi⟩
| horz ⟨i,hi⟩ ⟨j,hj⟩ => ⟨i * (size + size.succ) + size + j, by
  simp [Nat.mul_add, Nat.succ_mul, Nat.mul_succ, ←Nat.add_assoc]
  apply Nat.lt_of_succ_le
  rw [←Nat.succ_add]
  apply Nat.add_le_add _ (Nat.le_of_succ_le_succ hj)
  rw [←Nat.succ_add, Nat.add_assoc _ size, Nat.add_comm size, ←Nat.add_assoc]
  apply Nat.add_le_add_right
  rw [Nat.add_assoc, ←Nat.succ_add]
  apply Nat.add_le_add
  . apply Nat.mul_lt_mul_of_pos_right hi (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)
  . apply Nat.le_trans (Nat.add_le_add_left (Nat.le_of_lt hi) _)
    rw [←Nat.succ_mul]
    apply Nat.mul_le_mul_right _ hi
  ⟩

def ofFin : Fin (2 * (size * size.succ)) → DiamondIndex size
| ⟨k,hk⟩ =>
  let i := k / (size + size.succ)
  let j := k - i * (size + size.succ)
  if j < size then
    .vert ⟨i, sorry⟩ ⟨j, sorry⟩
  else
    .horz ⟨i, sorry⟩ ⟨j - size, sorry⟩


private def maxIdx {psize : Nat} : Fin psize.succ := ⟨psize, Nat.lt_succ_self _⟩
private def majorFins (size : Nat) : List (Fin size.succ) :=
  forIn' (m := Id) [0:size.succ] [] (fun x h y => .yield (⟨x,by exact h.2⟩ :: y))
private def middleMajorFins (size : Nat) : List ((_ : size > 0) ×' Fin size.succ) :=
  forIn' (m := Id) [1:size] [] (fun x h y => .yield (
    ⟨Nat.lt_of_le_of_lt (Nat.zero_le x) (by exact h.2), x, by exact Nat.le_step h.2⟩ :: y))
private def minorFins (size : Nat) : List (Fin size) :=
  forIn' (m := Id) [0:size] [] (fun x h y => .yield (⟨x,by exact h.2⟩ :: y))
private def middleMinorFins (size : Nat) : List (Fin size) :=
  match size with
  | 0 => []
  | psize+1 =>
  forIn' (m := Id) [1:psize] [] (fun x h y => .yield (⟨x,by exact Nat.le_step h.2⟩ :: y))

def all (size : Nat) : List (DiamondIndex size) :=
  majorFins size |>.bind fun i =>
    minorFins size |>.bind fun j =>
      [ .vert i j
      , .horz j i ]

/-- Half diamonds touching the puzzle's frame -/
def frame (size : Nat) : List (DiamondIndex size) :=
  minorFins size |>.bind fun i =>
    [ .vert 0 i
    , .vert maxIdx i
    , .horz i 0
    , .horz i maxIdx ]

/-- Full diamonds within the side/corner pieces -/
def border (size : Nat) : List (DiamondIndex size) :=
  middleMajorFins size |>.bind fun ⟨h,i⟩ =>
    match size, h with
    | _+1, _ =>
    [ .horz 0 i
    , .horz maxIdx i
    , .vert i 0
    , .vert i maxIdx ]

/-- Full diamonds not contained in side/corner pieces -/
def center (size : Nat) : List (DiamondIndex size) :=
  middleMajorFins size |>.bind fun ⟨_,i⟩ =>
    middleMinorFins size |>.bind fun j =>
      [ .vert i j
      , .horz j i ]

def isFrame : DiamondIndex size → Bool
| .vert i _ => i = 0 || i = maxIdx
| .horz _ j => j = 0 || j = maxIdx

def isBorder (di : DiamondIndex size) : Bool :=
  match size with
  | 0 => false
  | _+1 =>
  match di with
  | .horz i j => (i = 0 || i = maxIdx) && 0 < j && j < size
  | .vert i j => (j = 0 || j = maxIdx) && 0 < i && i < size

def isCenter : DiamondIndex size → Bool
| .vert i j => 0 < i && i < size && 0 < j.val && j < size.pred
| .horz i j => 0 < i.val && i < size.pred && 0 < j && j < size

instance : ToString (DiamondIndex size) where
  toString  | .horz i j => s!"horz {i} {j}"
            | .vert i j => s!"vert {i} {j}"

end DiamondIndex


namespace Color

def withBorder (borderColors centerColors : Nat) :=
  Fin (borderColors + centerColors + 1)

instance : DecidableEq (withBorder b c) := show DecidableEq (Fin _) from inferInstance
instance : Inhabited (withBorder b c) where default := ⟨0, Nat.zero_lt_succ _⟩

def frameColor : withBorder b c := ⟨0, by simp [withBorder]; exact Nat.zero_lt_succ _⟩
def borderColor (i : Fin b) : withBorder b c := ⟨i.val+1, by
  apply Nat.succ_le_succ
  simp
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  exact i.isLt⟩
def centerColor (i : Fin c) : withBorder b c := ⟨b+i.val+1, by
  apply Nat.succ_le_succ
  simp
  rw [Nat.add_assoc]
  apply Nat.add_le_add_left
  exact i.isLt⟩

def withBorder.isFrameColor : withBorder b c → Bool
| ⟨x,_⟩ => x == 0
def withBorder.isBorderColor : withBorder b c → Bool
| ⟨x,_⟩ => 1 ≤ x && x < b+1
def withBorder.isCenterColor : withBorder b c → Bool
| ⟨x,_⟩ => b+1 ≤ x

def borderColors : List (withBorder b c) :=
  List.fins b |>.map borderColor

def centerColors : List (withBorder b c) :=
  List.fins c |>.map centerColor

def allColors : List (withBorder b c) :=
  List.fins (b + c + 1)

instance : ToString (withBorder b c) where
  toString
  | ⟨i,_⟩ =>
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"[i]?
    |>.getD '*'
    |> (String.mk [·])

end Color


structure Tile (color : Type u) where
  (up right down left : color)
deriving BEq, Inhabited

inductive Sign
| plus  : Sign
| minus : Sign
deriving DecidableEq, Repr
def Sign.toString : Sign → String
| plus => "+"
| minus => "-"
instance : ToString Sign := ⟨Sign.toString⟩

structure SignedTile (color : Type u) extends Tile color where
  sign : Sign

namespace Tile

def toString [ToString c] (tile : Tile c) :=
  s!"┌{tile.up}┐\n{tile.left} {tile.right}\n└{tile.down}┘"

instance [ToString c] : ToString (Tile c) where
  toString := toString

def rotl : Tile c → Tile c
| {up,right,down,left} =>
  {up := right, right := down, down := left, left := up}

def rotln (n : Nat) : Tile c → Tile c := Function.iterate rotl n

def numRotations [BEq c] (tile1 tile2 : Tile c) :=
  if rotate 0 then some 0 else
  if rotate 1 then some 1 else
  if rotate 2 then some 2 else
  if rotate 3 then some 3 else
  none
where rotate n := rotln n tile2 == tile1

def eq [BEq c] (tile1 tile2 : Tile c) :=
  numRotations tile1 tile2 |>.isSome

def colors : Tile c → List c
| {up, right, down, left} => [up,right,down,left]

def hasColor [BEq c] (tile : Tile c) (color : c) : Bool :=
  tile.colors.contains color

def isCorner (tile : Tile (Color.withBorder b c)) : Bool :=
  rotate 0 || rotate 1 || rotate 2 || rotate 3
where rotate n :=
  let t := rotln n tile
  t.up.isFrameColor && t.right.isFrameColor &&
  t.down.isBorderColor && t.left.isBorderColor

def isSide (tile : Tile (Color.withBorder b c)) : Bool :=
  rotate 0 || rotate 1 || rotate 2 || rotate 3
where rotate n :=
  let t := rotln n tile
  t.up.isFrameColor && t.right.isBorderColor &&
  t.down.isCenterColor && t.left.isBorderColor

def isCenter (t : Tile (Color.withBorder b c)) : Bool :=
  t.up.isCenterColor && t.right.isCenterColor &&
  t.down.isCenterColor && t.left.isCenterColor

def validate (t : Tile (Color.withBorder b c)) : Bool :=
  t.isCorner || t.isSide || t.isCenter

def map (f : c → c') : Tile c → Tile c'
| {up, right, down, left} =>
  {up := f up, right := f right, down := f down, left := f left}

end Tile

structure TileBoard (size : Nat) (color : Type u) where
  board : Array (Array (Tile color))
  board_size :
    board.size = size ∧ ∀ i, (h : i < board.size) → (board[i]'h).size = size

namespace TileBoard

instance [ToString c] : ToString (TileBoard size c) where
  toString tile :=
    tile.board.toList.map (·.toList.map (toString))
    |> List.map (fun row =>
        row
        |>.map (·.splitOn "\n")
        |>.foldl (fun L1 L2 => List.zipWith (· ++ " " ++ ·) L1 L2) ["","",""]
        |> String.intercalate "\n"
      )
    |> String.intercalate "\n"

def tiles (tb : TileBoard size c) : List (Tile c) :=
  tb.board.foldr (·.toList ++ ·) []

def mapColors (f : c → c') : TileBoard size c → TileBoard size c'
| ⟨b, h⟩ => ⟨b.map (·.map (Tile.map f)), by simp [h]⟩

end TileBoard

structure DiamondBoard (size : Nat) (color : Type u) where
  board: Array color
  boardsize: board.size = 2 * (size * size.succ)

namespace DiamondBoard

def get (di : DiamondIndex size) (db : DiamondBoard size c) :=
  db.board.get (db.boardsize ▸ di.toFin)

def set (di : DiamondIndex size) (db : DiamondBoard size c) (color : c) : DiamondBoard size c :=
  ⟨ db.board.set (db.boardsize ▸ di.toFin) color
  , by simp [db.boardsize]⟩

def diamond_to_tile (dboard : DiamondBoard size c) (row col : Fin size) : Tile c :=
  {
    up    := dboard.get <| SquareIndex.up row col
    right := dboard.get <| SquareIndex.right row col
    down  := dboard.get <| SquareIndex.down row col
    left  := dboard.get <| SquareIndex.left row col
  }

def tileBoard (dboard : DiamondBoard size c) : TileBoard size c :=
  ⟨Array.init size (fun row =>
    Array.init size (fun col =>
      dboard.diamond_to_tile row col
    ))
  , by simp⟩

def expectFull (dboard : DiamondBoard size (Option c))
  : Except String (DiamondBoard size c) := do
  let board ← Array.initM (2 * (size * size.succ)) (fun idx => do
    match dboard.board.get (dboard.boardsize ▸ idx) with
    | none => throw s!"Diamond {DiamondIndex.ofFin idx}"
    | some d => return d)
  return ⟨board, sorry⟩

end DiamondBoard

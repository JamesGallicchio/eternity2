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

def ofFin : Fin (size*size) → SquareIndex size
| ⟨i,hi⟩ =>
  have : size > 0 := by
    cases size
    . simp at hi; contradiction
    . exact Nat.zero_lt_succ _
  ⟨ ⟨i / size, (Nat.div_lt_iff_lt_mul this).mpr hi⟩
  , ⟨i % size, Nat.mod_lt _ this⟩⟩

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

/-- List of indices at the k'th "layer" of the board, where 0 is the
border pieces and k/2 is the center piece (for odd sizes) /
pieces (for even sizes)
-/
def layerK (size : Nat) (k : Nat) : List (SquareIndex size) :=
  if k * 2 ≥ size then [] else
  all size |>.filter (fun ⟨i,j⟩ =>
    -- top/bottom row
    (i = k || i = size-k-1) && k ≤ j && j < (size-k)
    -- left/right column
    || (j = k || j = size-k-1) && k ≤ i && i < (size-k)
  )

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

structure WithBorder.Settings where
  border : List Nat
  center : List Nat

def WithBorder.Settings.size (s : WithBorder.Settings) :=
  1 + s.border.length + s.center.length

instance : ToString (WithBorder.Settings) where
  toString | {border,center} => s!"\{border := {border}, center := {center}}"

inductive WithBorder (s : WithBorder.Settings)
| frame
| border (n : Nat) (h : n ∈ s.border)
| center (n : Nat) (h : n ∈ s.center)
deriving DecidableEq, Inhabited, Hashable

def WithBorder.isFrame : WithBorder s → Bool
| frame => true
| _ => false
def WithBorder.isBorder : WithBorder s → Bool
| border _ _ => true
| _ => false
def WithBorder.isCenter : WithBorder s → Bool
| center _ _ => true
| _ => false

def borderColors : List (WithBorder s) := s.border.pmap (fun x h => .border x h) (λ _ => id)
def centerColors : List (WithBorder s) := s.center.pmap (fun x h => .center x h) (λ _ => id)

def allColors : List (WithBorder s) := .frame :: (borderColors ++ centerColors)

instance {s : WithBorder.Settings} : Inhabited (Fin s.size) where
  default := ⟨0, by simp [WithBorder.Settings.size, Nat.one_add, Nat.succ_add]; apply Nat.zero_lt_succ⟩

def WithBorder.Settings.toMap (s : WithBorder.Settings) : Std.HashMap (WithBorder s) (Fin s.size) :=
  Id.run do
    let mut acc := Std.HashMap.empty
    acc := acc.insert .frame ⟨0, by simp [size, Nat.one_add, Nat.succ_add]; apply Nat.zero_lt_succ⟩
    for (idx,x) in borderColors.mapIdx (fun idx x => (idx,x)) do
      have : idx < borderColors.length := sorry
      acc := acc.insert x ⟨1+idx, by simp [size, Nat.succ_add]; apply Nat.succ_lt_succ; apply Nat.lt_add_right; simp [borderColors] at this; exact this⟩
    for (idx,x) in centerColors.mapIdx (fun idx x => (idx,x)) do
      have : idx < centerColors.length := sorry
      acc := acc.insert x ⟨1+(@borderColors s).length+idx, by
        simp [size, Nat.succ_add]; apply Nat.succ_lt_succ
        simp [borderColors]; apply Nat.add_lt_add_left
        simp [centerColors] at this; exact this⟩
    return acc

instance : ToString (WithBorder s) where
  toString
  | .frame => "■"
  | .border i _
  | .center i _ =>
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"[i]?
    |>.map (String.mk [·])
    |>.getD ("`{toString i}`")

end Color


inductive Sign
| plus  : Sign
| minus : Sign
deriving DecidableEq, Repr
def Sign.toString : Sign → String
| plus => "+"
| minus => "-"
instance : ToString Sign := ⟨Sign.toString⟩

structure Tile (color : Type u) where
  (up right down left : color)
  sign : Option Sign
deriving Inhabited

namespace Tile

def toString [ToString c] (tile : Tile c) :=
  s!"┌{tile.up}┐\n{tile.left}{
    match tile.sign with
    | none => ' '
    | some .plus => '+'
    | some .minus => '-'
    }{tile.right}\n└{tile.down}┘"

instance [ToString c] : ToString (Tile c) where
  toString := toString

def rotl : Tile c → Tile c
| {up,right,down,left,sign} =>
  {up := right, right := down, down := left, left := up, sign}

def rotln (n : Nat) : Tile c → Tile c := Function.iterate rotl n

def numRotations [BEq c] (tile1 tile2 : Tile c) : Option (Fin 4) :=
  if rotate 0 then some 0 else
  if rotate 1 then some 1 else
  if rotate 2 then some 2 else
  if rotate 3 then some 3 else
  none
where rotate n :=
  let tile2 := rotln n tile2
  tile1.up    == tile2.up     &&
  tile1.right == tile2.right  &&
  tile1.down  == tile2.down   &&
  tile1.left  == tile2.left

def eq [BEq c] (tile1 tile2 : Tile c) :=
  numRotations tile1 tile2 |>.isSome

instance [BEq c] : BEq (Tile c) := ⟨eq⟩

def colors : Tile c → List c
| {up, right, down, left, sign := _} => [up,right,down,left]

def hasColor [BEq c] (tile : Tile c) (color : c) : Bool :=
  tile.colors.contains color

inductive ClassifyRes (c)
| corner (u r     : c)
| side   (u r d   : c)
| center (u r d l : c)

inductive ClassifyIsFrame (c) | frame | notframe (v : c)

def classifyGen {c c' : Type} [DecidableEq c] (f : c → ClassifyIsFrame c') (t : Tile c)
  : Option (Nat × ClassifyRes c') :=
  aux 0 |>.orElse fun () => aux 1 |>.orElse fun () => aux 2 |>.orElse fun () => aux 3
where aux (n : Nat) : Option (Nat × ClassifyRes c') :=
  match t.rotln n with
  | {up, right, down, left, sign := _} =>
  match f up, f right, f down, f left with
  | .notframe up, .notframe right, .frame, .frame =>
    some (n, .corner up right)
  | .notframe up, .notframe right, .notframe down, .frame =>
    some (n, .side up right down)
  | .notframe up, .notframe right, .notframe down, .notframe left =>
    some (n, .center up right down left)
  | _, _, _, _ => none

def classify {s} (t) :=
  classifyGen (fun c =>
    if @Color.WithBorder.isFrame s c then .frame else .notframe c)
    t
  |>.map (·.snd)

def mapToColorWithBorder [DecidableEq c] (f : c → ClassifyIsFrame Nat) (t : Tile c)
  : List Nat × List Nat × ((s : Color.WithBorder.Settings) → Except String (Tile (Color.WithBorder s))) :=
  let res := classifyGen f t
  let (newB, newC) :=
    (match res with
    | none => ([],[])
    | some (_, .corner u r) => ([u,r], [])
    | some (_, .side u r d) => ([u,d], [r])
    | some (_, .center u r d l) => ([], [u,r,d,l]))
  (newB, newC, fun s => do
  match ← res.map (Except.ok) |>.getD (Except.error "failed to classify") with
  | (n, .corner u r) =>
    if h:u ∈ s.border ∧ r ∈ s.border then
      return Tile.rotln ((4-n) % 4)
        { up := .border u h.1
        , right := .border r h.2
        , down := .frame
        , left := .frame
        , sign := t.sign }
    else throw s!"color configuration mismatch: s={s}; border {u}, {r} expected"
  | (n, .side u r d) =>
    if h:u ∈ s.border ∧ r ∈ s.center ∧ d ∈ s.border then
      return Tile.rotln ((4-n) % 4)
        { up := .border u h.1
        , right := .center r h.2.1
        , down := .border d h.2.2
        , left := .frame
        , sign := t.sign }
    else throw s!"color configuration mismatch: s={s}; border {u}, {d}, center {r} expected"
  | (n, .center u r d l) =>
    if h:u ∈ s.center ∧ r ∈ s.center ∧ d ∈ s.center ∧ l ∈ s.center then
      return Tile.rotln ((4-n) % 4)
        { up := .center u h.1
        , right := .center r h.2.1
        , down := .center d h.2.2.1
        , left := .center l h.2.2.2
        , sign := t.sign }
    else throw s!"color configuration mismatch: s={s}; center {u}, {r}, {d}, {l} expected"
  )


def isCorner (tile : Tile (Color.WithBorder s)) : Bool :=
  match classify tile with
  | .some (.corner _ _) => true
  | _ => false 

def isSide (tile : Tile (Color.WithBorder s)) : Bool :=
  match classify tile with
  | .some (.side _ _ _) => true
  | _ => false 

def isCenter (tile : Tile (Color.WithBorder s)) : Bool :=
  match classify tile with
  | .some (.center _ _ _ _) => true
  | _ => false 

def validate (tile : Tile (Color.WithBorder s)) : Bool :=
  (classify tile).isSome

def map (f : c → c') : Tile c → Tile c'
| {up, right, down, left, sign} =>
  {up := f up, right := f right, down := f down, left := f left, sign}

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
  tb.board.flatten.toList

def mapColors (f : c → c') : TileBoard size c → TileBoard size c'
| ⟨b, h⟩ => ⟨b.map (·.map (Tile.map f)), by simp [h]⟩

def tile (si : SquareIndex size) (board : TileBoard size c) :=
  have : si.row < board.board.size := board.board_size.1.symm ▸ si.row.isLt
  have : si.col < board.board[si.row].size := by
    have := board.board_size.2 si.row.1 this
    simp [this]
    exact si.col.isLt
  board.board[si.row][si.col]

def diamondAt [BEq c] (di : DiamondIndex size) (board : TileBoard size c) : Option c :=
  match di with
  | .vert ⟨i,hi⟩ ⟨j,hj⟩ =>
    if h : i = 0 then
      -- at top edge; return top of tile i,j
      have : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
      some <| board.tile ⟨⟨0, this⟩,⟨j,hj⟩⟩ |>.up
    else
      have : i-1 < size := Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h) (by rw [Nat.add_comm]; exact hi)
      if h : i < size then
        -- not at the bottom edge; return bottom of i-1,j
        let t1 := board.tile ⟨⟨i-1,this⟩,⟨j,hj⟩⟩
        let t2 := board.tile ⟨⟨i,h⟩,⟨j,hj⟩⟩
        if t1.down == t2.up then
          some t1.down
        else none
      else
        -- at bottom edge; return bottom of tile i-1,j
        some <| board.tile ⟨⟨i-1,this⟩,⟨j,hj⟩⟩ |>.down
  | .horz  ⟨i,hi⟩ ⟨j,hj⟩ =>
    if h : j = 0 then
      -- at left edge; return left of tile i,j
      have : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
      some <| board.tile ⟨⟨i,hi⟩,⟨0,this⟩⟩ |>.left
    else
      have : j-1 < size := Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h) (by rw [Nat.add_comm]; exact hj)
      if h : j < size then
        -- not at the right edge; return right of i,j-1
        let t1 := board.tile ⟨⟨i,hi⟩,⟨j-1,this⟩⟩
        let t2 := board.tile ⟨⟨i,hi⟩,⟨j,h⟩⟩
        if t1.right == t2.left then
          some t1.right
        else none
      else
        -- at right edge; return right of tile i,j-1
        some <| board.tile ⟨⟨i,hi⟩,⟨j-1,this⟩⟩ |>.right

end TileBoard

structure DiamondBoard (size : Nat) (color : Type u) where
  board: Array color
  boardsize: board.size = 2 * (size * size.succ)

namespace DiamondBoard

instance [Inhabited color] : Inhabited (DiamondBoard size color) :=
  ⟨⟨⟨List.replicate (2*(size*size.succ)) default⟩, by simp⟩⟩

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
    sign  := none
  }

def tileBoard (dboard : DiamondBoard size c) : TileBoard size c :=
  ⟨Array.init size (fun row =>
    Array.init size (fun col =>
      dboard.diamond_to_tile row col
    ))
  , by simp⟩

def ofTileBoard [BEq c] (tboard : TileBoard size c) : DiamondBoard size (Option c) :=
  { board := Array.init _ (fun idx => tboard.diamondAt (.ofFin idx))
  , boardsize := by simp }

def expectFull (dboard : DiamondBoard size (Option c))
  : Except String (DiamondBoard size c) := do
  let board ← Array.initM (2 * (size * size.succ)) (fun idx => do
    match dboard.board.get (dboard.boardsize ▸ idx) with
    | none => throw s!"Diamond {DiamondIndex.ofFin idx}"
    | some d => return d)
  return ⟨board, sorry⟩

end DiamondBoard

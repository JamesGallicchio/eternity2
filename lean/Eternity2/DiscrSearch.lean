
namespace Eternity2.DiscrSearch

inductive Dir | left | right
deriving Inhabited, DecidableEq, Repr

instance : ToString Dir := ⟨(Repr.reprPrec · 0 |>.pretty)⟩

inductive Step (α β) | fail | branch (a : Dir → α) | found (res : β)

def discrSearch {α β : Type} [Monad m] (depth : Nat) (init : α) (f : α → m (Step α β)) : m (Option β) :=
  aux depth init 0 (Nat.zero_le _)
where
  aux depth a n (h : n ≤ depth) := do
    match ← numRightsFixed depth a n h with
    | some b => return some b
    | none =>
    if h : n+1 ≤ depth then
      aux depth a (n+1) h
    else
      return none
  numRightsFixed depth a n (h : n ≤ depth) := do
    match ← f a with
    | .fail => return none
    | .found res =>
      if n = 0 then
        return some res
      else
        return panic! "should've already found this"
    | .branch a' =>
    match depth with
    | 0 => return none -- hit depth
    | depth+1 =>
    match n with
    | 0 => numRightsFixed depth (a' .left) 0 (Nat.zero_le _)
    | n+1 =>
    match ← numRightsFixed depth (a' .right) n (Nat.le_of_succ_le_succ h) with
    | some res => return some res
    | none =>
    if h : n+1 ≤ depth then
      numRightsFixed depth (a' .left) (n+1) (h)
    else -- not enough depth left to put n+1 rights, so must return none
      return none
termination_by aux depth _ n _ => depth-n

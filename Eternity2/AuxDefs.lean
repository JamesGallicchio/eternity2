import Std

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

def Array.init (n : Nat) (f : Fin n → α) : Array α := Id.run do
  let mut A := Array.mkEmpty n
  for h:i in [0:n] do
    A := A.push (f ⟨i,h.2⟩)
  return A

def Nat.sqrt (n : Nat) : Nat :=
  let guess := n / 2
  if guess = 0 then n else
  let rec iter (guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if h : guess ≤ next then
      guess
    else
      have : next < guess := Nat.gt_of_not_le h
      iter next
  iter guess
termination_by iter guess => guess

import Std

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

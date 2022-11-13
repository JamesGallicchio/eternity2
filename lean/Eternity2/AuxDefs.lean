import Std

def Function.iterate (f : α → α) : Nat → (α → α)
| 0 => id
| n+1 => iterate f n ∘ f

def Array.init (n : Nat) (f : Fin n → α) : Array α := Id.run do
  let mut A := Array.mkEmpty n
  for h:i in [0:n] do
    A := A.push (f ⟨i,h.2⟩)
  return A

theorem Array.init_zero : Array.init 0 f = #[] := by
  simp [init, Id.run, forIn', Std.Range.forIn']
  unfold Std.Range.forIn'.loop
  simp

theorem Array.init_succ {f : Fin n.succ → α}
  : Array.init n.succ f = (
      Array.init n (fun i => f ⟨i,Nat.lt_trans i.isLt (by exact Nat.le_refl _)⟩)
    ).push (f ⟨n, by exact Nat.le_refl _⟩)
  := by
  simp [init, Id.run, forIn', Std.Range.forIn']
  suffices ∀ i (hi : i ≤ n) o (_ : o.size = n-i),
    Std.Range.forIn'.loop (m := Id) 0 n.succ 1
      (fun i h r => ForInStep.yield (push r (f ⟨i, h.2⟩)))
      i.succ (n-i)
      (Nat.zero_le _)
      o
    = push (Std.Range.forIn'.loop (m := Id) 0 n 1
      (fun i h r => ForInStep.yield (push r (f ⟨i, Nat.le_step h.2⟩)))
      i (n-i)
      (Nat.zero_le _)
      o) (f ⟨n, Nat.lt_succ_self n⟩)
    by
    have := this n (Nat.le_refl _) #[] (by simp)
    simp at this
    exact this
  intro i hi o ho
  induction i generalizing o with
  | zero =>
    unfold Std.Range.forIn'.loop
    unfold Std.Range.forIn'.loop
    simp
  | succ i ih =>
    conv => lhs; unfold Std.Range.forIn'.loop
    conv => rhs; unfold Std.Range.forIn'.loop
    simp
    have hn := Nat.sub_lt_of_pos_le _ _ (Nat.succ_pos _) hi
    have hn' : n - Nat.succ i < Nat.succ n := Nat.le_step hn
    simp [hn, hn']
    have : n - Nat.succ i + 1 = n - i := by
      simp [Nat.sub_succ]
      rw [Nat.add_one, Nat.succ_pred_eq_of_pos (Nat.zero_lt_sub_of_lt hi)]
    suffices ∀ j, j = n - Nat.succ i + 1 →
      Std.Range.forIn'.loop (m := Id)  _ _ _ _ _ j (Nat.zero_le _) _
      = push (Std.Range.forIn'.loop (m := Id) _ _ _ _ _ j (Nat.zero_le _) _) _
      from this _ rfl
    intro j hj
    rw [this] at hj
    cases hj
    apply ih
    exact Nat.le_of_lt hi
    simp [ho, this]

@[simp]
theorem Array.size_init : (Array.init n f).size = n := by
  induction n
  . simp [size, init_zero]
  . next ih =>
    simp [init_succ]; exact ih

private theorem thing (hi : i < n) (h : n = n')
  : h ▸ (⟨i,hi⟩ : Fin n) = ⟨i, h ▸ hi⟩
  := by cases h; simp

--set_option pp.all true in
@[simp]
theorem Array.get_init : (Array.init n f)[i] = f (@size_init n _ f ▸ i) := by
  induction n with
  | zero => simp at i; exact i.elim0
  | succ n ih =>
    simp [init_succ, get_push]
    split
    next h =>
      have := @ih (fun i => f ⟨i,Nat.lt_trans i.isLt (by exact Nat.le_refl _)⟩) ⟨i,by simp; assumption⟩
      cases i; case mk i hi =>
      simp at this ⊢
      rw [this]
      congr
      simp [thing]
    next h =>
      cases i; case mk i hi =>
      simp at h
      have : i = n := Nat.le_antisymm
        (Nat.le_of_succ_le_succ (by rw [size_init] at hi; exact hi))
        h
      cases this
      congr
      simp [thing]

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

def List.distinct [DecidableEq α] (L : List α) : List α :=
  L.foldl (·.insert ·) []

def List.isDistinct [DecidableEq α] : List α → Bool
| [] => true
| x::xs => !xs.contains x && xs.isDistinct

def List.fins (n : Nat) : List (Fin n) :=
  finsAux n (Nat.le_refl _) []
where
  finsAux : (i : Nat) → i ≤ n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc
  | i+1, h, acc => finsAux i (Nat.le_of_lt h) (⟨i,h⟩ :: acc)


def parForIn [ForIn IO σ α] (xs : σ) (f : α → IO PUnit) : IO PUnit := do
  let mut tasks := #[]
  for x in xs do
    tasks := tasks.push (← IO.asTask (f x))
  tasks.forM (ofExcept ·.get)

syntax "parallel " "for " ident " in " termBeforeDo " do " doSeq : doElem
macro_rules
  | `(doElem| parallel for $x in $xs do $seq) => `(doElem| parForIn $xs fun $x => do $seq)

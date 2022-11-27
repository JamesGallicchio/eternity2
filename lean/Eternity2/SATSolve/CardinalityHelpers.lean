import Eternity2.SATSolve.EncCNF

namespace EncCNF

def atMostK (lits : Array Literal) (k : Nat) : EncCNF Unit := do
  -- if `i` < `∑ j' ≤ j, lits[j']` then `temps[i][j]`
  let temps ← mkTempBlock [k+1, lits.size]

  -- lits[j] -> temps[0][j]
  for h:j in [0:lits.size] do
    have : j < lits.size := by simp at h; exact h.2
    have : 0 < k+1 := Nat.zero_lt_succ _
    addClause [lits[j].not, ⟨temps[0][j], false⟩]

  -- temps[i][j] -> temps[i][j+1]
  for h:i in [0:k+1] do
    have : i < k+1 := by simp at h; exact h.2
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause [⟨temps[i][j], true⟩, ⟨temps[i][j+1], false⟩]

  -- temps[i][j] ∧ lits[j+1] -> temps[i+1][j+1]
  for h:i in [0:k] do
    have : i+1 < k+1 := by simp at h; exact Nat.succ_lt_succ h.2
    have : i < k+1 := Nat.lt_of_succ_lt this
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause [⟨temps[i][j], true⟩, lits[j+1].not, ⟨temps[i+1][j+1],false⟩]

  -- require not `temps[k][lits.size-1]`
  --   ==> not (`k` < `∑ j', lits[j']`)
  --   <=> `k` ≥ `∑ j', lits[j']`
  if h:lits.size > 0 then
    have : lits.size-1 < lits.size := Nat.sub_lt_self (by decide) h
    addClause [⟨temps[k][lits.size-1], true⟩]

def atLeastK (lits : Array Literal) (k : Nat) : EncCNF Unit := do
  match k with
  | 0 => return -- Always trivially true
  | k+1 =>
  -- if `temps[i][j]` then `i` < `∑ j' ≤ j, lits[j']`
  let temps ← mkTempBlock [k+1, lits.size]

  -- temps[0][0] -> lits[0]
  if h:lits.size > 0 then
    have : 0 < k+1 := Nat.zero_lt_succ _
    addClause [⟨temps[0][0], true⟩, lits[0]]
    for h:i in [1:k+1] do
      have : i < k+1 := h.2
      addClause [⟨temps[i][0], true⟩]

  -- temps[i][j+1] ∧ ¬lits[j+1] -> temps[i][j]
  for h:i in [0:k+1] do
    have : i < k+1 := by simp at h; exact h.2
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause [⟨temps[i][j+1], true⟩, lits[j+1], ⟨temps[i][j], false⟩]

  -- temps[i+1][j+1] -> temps[i][j]
  for h:i in [0:k] do
    have : i+1 < k+1 := by simp at h; exact Nat.succ_lt_succ h.2
    have : i < k+1 := Nat.lt_of_succ_lt this
    for h:j in [0:lits.size-1] do
      have : j+1 < lits.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < lits.size := Nat.lt_of_succ_lt this
      addClause [⟨temps[i+1][j+1], true⟩, ⟨temps[i][j], false⟩]

  -- require `temps[k][lits.size-1]` true
  --   ==> `k` < `∑ j', lits[j']`
  --   <=> `k+1` ≤ `∑ j', lits[j']`
  if h:lits.size > 0 then
    have : lits.size-1 < lits.size := Nat.sub_lt_self (by decide) h
    addClause [⟨temps[k][lits.size-1], false⟩]

def equalK (lits : Array Literal) (k : Nat) : EncCNF Unit := do
  atMostK lits k
  atLeastK lits k

def atMostOneList (lits : List Literal) : EncCNF Unit := do
  match lits with
  | []                      => return
  | l1 :: []                => atMostK (Array.mkArray1 l1) 1
  | l1 :: l2 :: []          => atMostK (Array.mkArray2 l1 l2) 1
  | l1 :: l2 :: l3 :: rlits =>
    let t ← mkTemp
    atMostOneList (rlits.append [⟨t, false⟩]) -- not sure if i should be
    atMostOneList (⟨t, false⟩ :: rlits)       --    including both clauses?
    atMostK (Array.mkArray4 l1 l2 l3 ⟨t, true⟩) 1
termination_by atMostOneList lits => lits.length

def atMostOne (lits : Array Literal) : EncCNF Unit := do
  atMostOneList lits.toList

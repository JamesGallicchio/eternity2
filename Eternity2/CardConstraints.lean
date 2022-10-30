import Eternity2.EncCNF

namespace EncCNF

def sinzBlock (vars : Array Var) (k : Nat) : EncCNF (VarBlock [k+1, vars.size]) := do
  -- ∀ i, `temps[i][j]` iff `i` < `∑ j' ≤ j, vars[j']`
  let temps ← mkTempBlock [k+1, vars.size]

  -- vars[j] -> temps[0][j]
  for h:j in [0:vars.size] do
    have : j < vars.size := by simp at h; exact h.2
    have : 0 < temps.hdLen := Nat.zero_lt_succ _
    addClause [⟨vars[j], true⟩, ⟨temps[0][j], false⟩]
  
  -- temps[i][j] -> temps[i][j+1]
  for h:i in [0:k+1] do
    have : i < temps.hdLen := by simp at h; exact h.2
    for h:j in [0:vars.size-1] do
      have : j+1 < temps[i].hdLen := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < temps[i].hdLen := Nat.lt_of_succ_lt this
      addClause [⟨temps[i][j], true⟩, ⟨temps[i][j+1], false⟩]
  
  -- temps[i][j] ∧ vars[j+1] -> temps[i+1][j+1]
  for h:i in [0:k] do
    have : i+1 < temps.hdLen := by simp at h; exact Nat.succ_lt_succ h.2
    have : i < temps.hdLen := Nat.lt_of_succ_lt this
    for h:j in [0:vars.size-1] do
      have : j+1 < vars.size := by simp at h; exact Nat.add_lt_of_lt_sub h.2
      have : j < vars.size := Nat.lt_of_succ_lt this
      addClause [⟨temps[i][j], true⟩, ⟨vars[j+1], true⟩, ⟨temps[i+1][j+1],false⟩]

  return temps

def atMostK (vars : Array Var) (k : Nat) : EncCNF Unit := do
  -- build the Sinz implication blocks
  let temps ← sinzBlock vars k
  -- require `temps[k][vars.size-1]` false
  --   ==> `k` ≥ `∑ j', vars[j']`
  if h:vars.size > 0 then
    have : vars.size-1 < vars.size := Nat.sub_lt_self (by decide) h
    addClause [⟨temps[k][vars.size-1], true⟩]

def atLeastK (vars : Array Var) (k : Nat) : EncCNF Unit := do
  match k with
  | 0 => return -- Trivially ≥ 0
  | k+1 =>
    -- build the Sinz implication blocks
    let temps ← sinzBlock vars k
    -- require `temps[k][vars.size-1]` true
    --   ==> `k` < `∑ j', vars[j']`
    --   ==> `k+1` ≤ `∑ j', vars[j']`
    if h:vars.size > 0 then
      have : vars.size-1 < vars.size := Nat.sub_lt_self (by decide) h
      addClause [⟨temps[k][vars.size-1], false⟩]

def equalK (vars : Array Var) (k : Nat) : EncCNF Unit := do
  -- build the Sinz implication blocks
  let temps ← sinzBlock vars k

  if h:vars.size > 0 then
    have : vars.size-1 < vars.size := Nat.sub_lt_self (by decide) h

    -- require `temps[k-1][vars.size-1]` true
    --   ==> `k-1` < `∑ j', vars[j']`
    --   ==> `k` ≤ `∑ j', vars[j']`
    if h:k > 0 then
      have : k-1 < k := Nat.sub_lt_self (by decide) h
      have : k-1 < k+1 := Nat.lt_succ_of_lt this
      addClause [⟨temps[k-1][vars.size-1], false⟩]

    -- require `temps[k][vars.size-1]` false
    --   ==> `k` ≥ `∑ j', vars[j']`
    addClause [⟨temps[k][vars.size-1], true⟩]


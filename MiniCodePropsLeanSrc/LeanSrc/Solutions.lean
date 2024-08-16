import Mathlib

lemma soln_prop_08 (k:Nat) (m: Nat) (n: Nat) : ((k + m) - (k + n) = m - n) := by
  exact Nat.add_sub_add_left k m n

import Mathlib
-- a few examples to use when prompting an LLM for few-shot generation

inductive MyTree (α: Type) where
| leaf : MyTree α
| node : MyTree α → α → MyTree α  →  MyTree α

def tree_size : MyTree α → ℕ
  | .leaf => 1
  | .node l _x r => 1 + (tree_size l) + (tree_size r)

def balanced : MyTree α → Prop
  | .leaf => true
  | .node l _x r => ((tree_size l) = (tree_size r)) ∧ (balanced l) ∧ (balanced r)

theorem balanced_tree_size_odd (t: MyTree α) (hb: balanced t): Odd (tree_size t) := by
  cases t with
  | leaf => simp [tree_size]
  | node p x q =>
    unfold tree_size
    unfold balanced at hb
    simp [hb.1]

def swap_branches : MyTree α → MyTree α
  | MyTree.leaf => MyTree.leaf
  | MyTree.node p x q => MyTree.node q x p

theorem swap_preserves_balance (t: MyTree α) (hb: balanced t): balanced (swap_branches t) := by
  cases t with
  | leaf => simp [swap_branches, balanced]
  | node p x q =>
    unfold balanced at hb
    simp [swap_branches, balanced]
    exact ⟨Eq.symm hb.1, hb.2.2, hb.2.1⟩

inductive PairList where
| empty : PairList
| node  : Nat → Nat → PairList → PairList

def len_pairlist : PairList → Nat
| .empty => 0
| .node _n1 _n2 l => len_pairlist l + 2

lemma even_plus_two (x: Nat) (h: Even x): Even (x + 2) := by
  unfold Even at h
  rcases h with ⟨y, hy⟩
  use y + 1
  linarith [hy]

theorem len_pairlist_even (l: PairList): Even (len_pairlist l) := by
  generalize hl: len_pairlist l = pl
  induction pl using Nat.strong_induction_on generalizing l with
  | h n ih => cases l with
    | empty => simp [len_pairlist] at hl; simp [←hl];
    | node n1 n2 l2 =>
      unfold len_pairlist at hl
      simp [←hl]
      apply even_plus_two
      exact ih (len_pairlist l2) (by linarith [hl]) l2 (by rfl)

-- from koen/Sort.hs
import Mathlib
import Init.Data.List
import Mathlib.Algebra.Parity

-- here are the translated koen/SortUtils.hs
def deleteFirst [DecidableEq α]: α → List α → List α
  | _, [] => []
  | n, x::xs => if n == x then xs else x::(deleteFirst n xs)

def isPermutation [DecidableEq α] : List α → List α → Bool
| [], ys => (ys == [])
| x::xs, ys => x ∈ ys && (isPermutation xs (deleteFirst x ys))

def ordered : List Nat -> Bool
| []       => True
| [_x]     => True
| x::y::xs => x <= y && ordered (y::xs)

def uniqsorted : List Nat -> Bool
| []       => True
| [_x]     => True
| x::y::xs => x < y && uniqsorted (y::xs)

def count [DecidableEq α] : α → List α → Nat
| _x, [] => 0
| x, y::ys => if x == y then 1 + (count x ys) else count x ys

def deleteAll [DecidableEq α]: α → List α → List α
  | _, [] => []
  | n, x::xs => if n == x then (deleteAll n xs) else x::(deleteAll n xs)

-- end of SortUtils, start of Sort.hs

def third : Nat → Nat
| 0 => 0
| 1 => 0
| 2 => 0
| n + 3 => 1 + (third n)

def twoThirds : Nat → Nat
| 0 => 0
| 1 => 0
| 2 => 0
| n + 3 => 2 + (twoThirds n)

def insert' : Nat → List Nat → List Nat
| x, [] => [x]
| x, y::xs => if x <= y then x::y::xs else y::(insert x xs)

def isort: List Nat → List Nat
| [] => []
| x::xs => insert' x (isort xs)

def prop_ISortSorts (xs: List Nat) := ordered (isort xs) == True
def prop_ISortCount (x: Nat) (xs: List Nat) := count x (isort xs) == count x xs
def prop_ISortPermutes (xs: List Nat) := isPermutation (isort xs) xs == True

--------------------------------------------------------------------------------
-- returns true if more work is needed, plus a more-sorted list
def bubble : List Nat → (Bool × List Nat)
| x::y::xs =>
    have c : Bool := x <= y
    have x' := if c then x else y
    have y' := if c then y else x
    have (b, ys) := bubble (y'::xs)
    (not c||b, x'::ys)
| xs => (False, xs)
termination_by xs => xs.length

-- stolen from Lean source: https://github.com/leanprover/lean4/commit/1620987b6ce40c98aaca78393e1ef15b261e6400
def bubsort (xs : List Nat) : {l' : List Nat // xs.length = l'.length} :=
  match xs with
  | [] => ⟨[], rfl⟩
  | x :: xs =>
    match bubsort xs with
    | ⟨[], h⟩ => ⟨[x], by simp[h]⟩
    | ⟨y :: ys, h⟩ =>
      if y < x then
        have : Nat.succ (List.length ys) < Nat.succ (List.length xs) := by rw [h, List.length_cons]; apply Nat.lt_succ_self
        let ⟨zs, he⟩ := bubsort (x :: ys)
        ⟨y :: zs, by simp[h, ← he]⟩
      else
        ⟨x :: y :: ys, by simp[h]⟩
termination_by xs.length

def bubblesort (xs: List Nat) : List Nat :=
  bubsort xs

def prop_BubSortSorts (xs: List Nat) := ordered (bubsort xs) == true
def prop_BubSortCount (x: Nat) (xs: List Nat) := count x (bubsort xs) == count x xs
def prop_BubSortPermutes (xs: List Nat) := isPermutation (bubsort xs) xs == true
def prop_BubSortIsSort (xs: List Nat) := bubblesort xs == isort xs

inductive MyHeap where
| nil : MyHeap
| node : MyHeap → Nat → MyHeap  →  MyHeap

def hmerge : MyHeap  → MyHeap  → MyHeap
| MyHeap.nil, q => q
| p, MyHeap.nil => p
| MyHeap.node p x q, MyHeap.node r y s =>
  if x <= y then MyHeap.node (hmerge q (MyHeap.node r y s)) x p
            else MyHeap.node (hmerge (MyHeap.node p x q) s) y r

def hpairwise : List MyHeap → List MyHeap
| p::q::qs => (hmerge p q)::hpairwise qs
| ps => ps

lemma hpairwise_desc (ps: List MyHeap): List.length (hpairwise ps) ≤ List.length ps := by
  generalize hl: ps.length = len
  induction len using Nat.strong_induction_on generalizing ps with
  | h len2 ih =>
    match ps with
      | [] => unfold hpairwise; simp
      | q1::qs1 => match qs1 with
        | [] => unfold hpairwise; rw [←hl]
        | q2::qs2 => unfold hpairwise; rw [← hl, List.length_cons, List.length_cons, List.length_cons,Nat.succ_le_succ_iff]
                     rw [List.length_cons, List.length_cons] at hl
                     have hl3 := Nat.lt_of_succ_lt (Nat.lt_of_succ_le (Nat.le_of_eq hl))
                     exact Nat.le.step (ih (qs2.length) hl3 qs2 rfl)

def hmerging : List MyHeap → MyHeap
| [] => MyHeap.nil
| [p] => p
| p::q::ps =>
    have : List.length (hpairwise (p :: q :: ps)) < Nat.succ (Nat.succ (List.length ps)) := by
      unfold hpairwise
      rw [List.length_cons, Nat.succ_lt_succ_iff, Nat.lt_succ]
      exact hpairwise_desc _
    hmerging (hpairwise (p::q::ps))
termination_by ps => ps.length

def toHeap : List Nat → MyHeap
| xs => hmerging (xs.map (fun x => MyHeap.node MyHeap.nil x MyHeap.nil))

def numElem : MyHeap → Nat
| MyHeap.nil => 0
| MyHeap.node p _x q => 1 + numElem p + numElem q

lemma numElem_lt_subHeaps  (q r: MyHeap) {x: Nat}: numElem q < numElem (MyHeap.node q x r) ∧ numElem r < numElem (MyHeap.node q x r) := by
  have h': numElem (MyHeap.node q x r) = 1 + numElem q + numElem r; rfl
  rw [h'];
  exact ⟨by linarith, by linarith⟩;

lemma merge_elems (p q: MyHeap): numElem p + numElem q = numElem (hmerge p q) := by
  generalize hsp: numElem p = sp
  generalize hsq: numElem q = sq
  generalize hspq: numElem (hmerge p q) = spq
  induction sp using Nat.strong_induction_on generalizing p q sq spq with
  | h sp2 ih =>   induction sq using Nat.strong_induction_on generalizing p q sp2 spq with
    | h sq2 ih2 =>
    rw [←hsp, ← hsq, ← hspq];
    unfold hmerge;
    split;
    case h_1 _ _;
      unfold numElem; rw [Nat.add_comm, Nat.add_zero];
    case h_2 _ _;
      unfold numElem; rw [Nat.add_zero];
    case h_3 _ _ pl x pr ql y qr;
      split;
        unfold numElem;
        suffices h': numElem (hmerge pr (MyHeap.node ql y qr)) = numElem pr + (1 + numElem ql + numElem qr);
          rw[h']; linarith;
        rw [←hsp] at ih;
        exact Eq.symm (ih (numElem pr) (numElem_lt_subHeaps _ _).2 pr (MyHeap.node ql y qr) rfl
          (numElem (MyHeap.node ql y qr)) rfl (numElem (hmerge pr (MyHeap.node ql y qr))) rfl);
      --case 2
        unfold numElem;
        suffices h': numElem (hmerge (MyHeap.node pl x pr) qr) = numElem qr + (1 + numElem pl + numElem pr);
          rw[h']; linarith;
        rw [←hsq] at ih2;
        have h':= ih2 (numElem qr) (numElem_lt_subHeaps _ _).2 sp2 ih (MyHeap.node pl x pr) qr hsp rfl
          (numElem (hmerge (MyHeap.node pl x pr) qr)) rfl;
        rw [←hsp] at h';
        suffices h'': 1 + numElem pl + numElem pr = numElem (MyHeap.node pl x pr);
          rw [h'']; linarith;
        rfl;

lemma numElem_merge_branches_lt (p q: MyHeap) (x: Nat): numElem (hmerge p q) < numElem (MyHeap.node p x q) := by
  rw [←merge_elems _ _];
  have h': numElem (MyHeap.node p x q) = 1 + numElem p + numElem q; rfl
  rw [h']
  linarith;

def toList : MyHeap → List Nat
| MyHeap.nil => []
| MyHeap.node p x q =>
    have _h := numElem_merge_branches_lt p q x
    x :: toList (hmerge p q)
termination_by hp => numElem hp

def hsort : List Nat → List Nat
 | xs => toList (toHeap xs)

def prop_HSortSorts (xs: List Nat) := ordered (hsort xs) == True
def prop_HSortCount (x: Nat) (xs: List Nat) := count x (hsort xs) == count x xs
def prop_HSortPermutes (xs: List Nat) := isPermutation (hsort xs) xs == True
def prop_HSortIsSort (xs: List Nat) := hsort xs == isort xs


def hinsert : Nat → MyHeap → MyHeap
| x, h => hmerge (MyHeap.node MyHeap.nil x MyHeap.nil) h

def toHeap2 : List Nat → MyHeap
| [] => MyHeap.nil
| x::xs => hinsert x (toHeap2 xs)

def hsort2 : List Nat → List Nat
| xs => toList (toHeap2 xs)

def prop_HSort2Sorts (xs: List Nat) := ordered (hsort2 xs) == True
def prop_HSort2Count (x: Nat) (xs: List Nat) := count x (hsort2 xs) == count x xs
def prop_HSort2Permutes (xs: List Nat) := isPermutation (hsort2 xs) xs == True
def prop_HSort2IsSort (xs: List Nat) := hsort2 xs == isort xs

def risers : List Nat → List (List Nat)
| [] => []
| [x] => [[x]]
| x::y::xs => if x <= y then
      match (risers (y::xs)) with
      | ys::yss => (x::ys)::yss
      | _ => []
    else
      [x]::(risers (y::xs))

def lmerge : List Nat → List Nat → List Nat
| [], ys => ys
| xs, [] => xs
| x::xs, y::ys => if  x <= y  then
      x::(lmerge xs (y::ys))
    else
      y::(lmerge (x::xs) ys)

def pairwise : List (List Nat) → List (List Nat)
| xs::ys::xss => lmerge xs ys :: pairwise xss
| xss => xss

def pairwise_len : List (List Nat) → Nat
| xs => if (Odd xs.length) then xs.length/2 + 1 else xs.length/2

lemma len_pairwise (xs: List (List Nat)): 2 * (pairwise xs).length = (if (Odd xs.length) then xs.length + 1 else xs.length) := by
  generalize hxl : xs.length = xl;
  split_ifs with h1;
  case pos;
    induction xl using Nat.strong_induction_on generalizing xs with
    | h xls ih =>
        rw [← hxl] at h1;
        cases xs with
        | nil => simp at h1;
        | cons head2 tail2 =>
          cases tail2 with
          | nil => unfold pairwise; simp at hxl; rw [←hxl]; simp;
          | cons head3 tail3 =>
            unfold pairwise;
            rw [←hxl, List.length_cons, List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _]
            ring_nf;
            simp;
            have hodd: Odd tail3.length := by
              rw [List.length_cons, List.length_cons, Nat.succ_eq_add_one _, Nat.add_assoc, Nat.odd_add] at h1;
              apply h1.2; simp;
            have tmp := ih tail3.length (by rw [←hxl]; simp; linarith;) tail3 rfl hodd
            ring_nf at tmp;
            rw [tmp];
            ring_nf;
  case neg;
    induction xl using Nat.strong_induction_on generalizing xs with
    | h xls ih =>
        rw [← hxl] at h1;
        cases xs with
        | nil => unfold pairwise; simp [← hxl]
        | cons head2 tail2 =>
          cases tail2 with
          | nil => simp at h1;
          | cons head3 tail3 =>
            unfold pairwise;
            rw [←hxl, List.length_cons, List.length_cons, List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _];
            ring_nf;
            simp;
            simp at h1;
            have heven: Even tail3.length := by
              rw [Nat.add_assoc, Nat.even_add] at h1;
              apply h1.2; simp;
            simp at ih;
            have tmp := ih tail3.length (by rw [←hxl]; simp; linarith;) tail3 rfl heven
            ring_nf at tmp;
            exact tmp;

lemma merge_term : (pairwise (xs::ys::xss)).length < (xs::ys::xss).length := by
    suffices h': 2* List.length (pairwise (xs :: ys :: xss)) < 2 * List.length (xs :: ys :: xss)
    case h';
      rw [ len_pairwise _];
      split_ifs with hparity;
      case pos;
        simp;
        ring_nf;
        linarith;
      case neg;
        simp;
    linarith [h'];

def mergingbu2 : List (List Nat) → List Nat
| [] => []
| [xs] => xs
| xs::ys::xss =>
  have _h: (pairwise (xs::ys::xss)).length < (xs::ys::xss).length := by
    suffices h': 2* List.length (pairwise (xs :: ys :: xss)) < 2 * List.length (xs :: ys :: xss)
    case h';
      rw [ len_pairwise _];
      split_ifs with hparity;
      case pos;
        simp;
        ring_nf;
        linarith;
      case neg;
        simp;
    linarith [h'];
  mergingbu2 (pairwise (xs::ys::xss))
termination_by xss => xss.length

def msortbu2 : List Nat → List Nat
| xs => mergingbu2 (risers xs)

-- Bottom-up merge sort, using a total risers function
def prop_MSortBU2Sorts (xs: List Nat) := ordered (msortbu2 xs) == true
def prop_MSortBU2Count (x: Nat) (xs: List Nat) := count x (msortbu2 xs) == count x xs
def prop_MSortBU2Permutes (xs: List Nat) := isPermutation (msortbu2 xs) xs == true
def prop_MSortBU2IsSort (xs: List Nat) := msortbu2 xs == isort xs


def mergingbu : List (List Nat) → List Nat
| [] => []
| [xs] => xs
| xs::ys::xss =>
  have _h: (pairwise (xs::ys::xss)).length < (xs::ys::xss).length := by
    suffices h': 2* List.length (pairwise (xs :: ys :: xss)) < 2 * List.length (xs :: ys :: xss)
    case h';
      rw [ len_pairwise _];
      split_ifs with hparity;
      case pos;
        simp;
        ring_nf;
        linarith;
      case neg;
        simp;
    linarith [h'];
  mergingbu (pairwise (xs::ys::xss))
termination_by xss => xss.length

def msortbu : List Nat → List Nat
| xs => mergingbu (xs.map (fun x => [x]))

def prop_MSortBUSorts (xs: List Nat) := ordered (msortbu xs) == true
def prop_MSortBUCount (x: Nat) (xs: List Nat) := count x (msortbu xs) == count x xs
def prop_MSortBUPermutes (xs: List Nat) := isPermutation (msortbu xs) xs == true
def prop_MSortBUIsSort (xs: List Nat) := msortbu xs == isort xs

def msorttd : List Nat → List Nat
| [] => []
| [x] => [x]
| x::y::xs =>
  let k:= (x::y::xs).length/2
  have _h: Nat.succ (Nat.succ (List.length xs)) / 2 < Nat.succ (Nat.succ (List.length xs)) := by
    rw [Nat.succ_eq_add_one _];
    ring_nf;
    simp [Nat.succ_eq_add_one _];
    ring_nf;
    calc 1 + xs.length/2 ≤ 1 + xs.length := by simp; exact Nat.div_le_self (List.length xs) 2;
         _               < 2 + xs.length := by simp;
  lmerge (msorttd ((x::y::xs).take k)) (msorttd ((x::y::xs).drop k))
termination_by xs => xs.length

def prop_MSortTDSorts (xs: List Nat) := ordered (msorttd xs) == true
def prop_MSortTDCount (x: Nat) (xs: List Nat) := count x (msorttd xs) == count x xs
def prop_MSortTDPermutes (xs: List Nat) := isPermutation (msorttd xs) xs == true
def prop_MSortTDIsSort (xs: List Nat) := msorttd xs == isort xs

def half : Nat → Nat
| 0 => 0
| 1 => 0
| x + 2 => 1 + (half x)

lemma half_lt: half x ≤ x := by
  induction x using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => unfold half; simp;
    | succ nm1 =>
      cases nm1 with
      | zero => unfold half; simp;
      | succ nm2 =>
        unfold half;
        have tmp := ih nm2 (by exact Nat.le.step Nat.le.refl);
        ring_nf;
        calc 1 + half nm2 ≤ 1 + nm2  := Nat.add_le_add (@Nat.le.refl 1) tmp
             _           ≤  2 + nm2  := by simp

def nmsorttd : List Nat → List Nat
| [] => []
| [x] => [x]
| x::y::xs =>
  let k:= half ((x::y::xs).length)
  have _h: half (Nat.succ (Nat.succ (List.length xs))) < Nat.succ (Nat.succ (List.length xs)) := by
    rw [Nat.succ_eq_add_one _];
    ring_nf;
    rw [Nat.add_comm];
    unfold half;
    ring_nf;
    calc 1 + half (xs.length) ≤ 1 + xs.length := by simp; exact half_lt;
         _               < 2 + xs.length := by simp;
  have _h': Nat.succ (Nat.succ (List.length xs)) - half (Nat.succ (Nat.succ (List.length xs))) <
  Nat.succ (Nat.succ (List.length xs)) := by
    suffices h': 0 < half (Nat.succ (Nat.succ (List.length xs)))
    case h';
      unfold half;simp;
    refine Nat.sub_lt ?h h'
    simp;
  lmerge (nmsorttd ((x::y::xs).take k)) (nmsorttd ((x::y::xs).drop k))
termination_by xs => xs.length

def prop_NMSortTDSorts (xs: List Nat) := ordered (nmsorttd xs) == true
def prop_NMSortTDCount (x: Nat) (xs: List Nat) := count x (nmsorttd xs) == count x xs
def prop_NMSortTDPermutes (xs: List Nat) := isPermutation (nmsorttd xs) xs == true
def prop_NMSortTDIsSort (xs: List Nat) := nmsorttd xs == isort xs

mutual
  def evens : List Nat → List Nat
  | [] => []
  | x::xs => x::(odds xs)
--
  def odds : List Nat → List Nat
  | [] => []
  | _x::xs => evens xs
end

lemma len_evens_le {xs: List Nat}: (evens xs).length ≤ xs.length := by
  generalize hxsl: xs.length = xsl
  induction xsl using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => unfold evens; simp;
    | cons head1 tail1 =>
      unfold evens;
      cases tail1 with
      | nil => unfold odds; rw[← hxsl];
      | cons head2 tail2 =>
        unfold odds;
        rw [List.length_cons, List.length_cons] at hxsl;
        rw [← hxsl, List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _];
        simp;
        have h': List.length tail2 < n := by rw [← hxsl, Nat.succ_eq_add_one _]; linarith;
        exact Nat.le.step (ih (List.length tail2) h' rfl);

lemma len_odds_le {xs: List Nat}: (odds xs).length ≤ xs.length := by
  generalize hxsl: xs.length = xsl
  induction xsl using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => unfold odds; simp;
    | cons head1 tail1 =>
      unfold odds;
      cases tail1 with
      | nil => unfold evens; simp;
      | cons head2 tail2 =>
        unfold evens;
        rw [List.length_cons, List.length_cons] at hxsl;
        rw [← hxsl, List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _];
        simp;
        have h': List.length tail2 < n := by rw [← hxsl, Nat.succ_eq_add_one _]; linarith;
        exact Nat.le.step (ih (List.length tail2) h' rfl);

def sort2 (a b: Nat): List Nat := if a ≤ b then [a,b] else [b, a]

def pairs : List Nat → List Nat → List Nat
| [], ys => ys
| xs, [] => xs
| x::xs, y::ys => (sort2 x y) ++ (pairs xs ys)

def stitch : List Nat → List Nat → List Nat
| [], ys => ys
| x::xs, ys => x::(pairs xs ys)

lemma bmerge_term (a b: Nat) (as bs: List Nat) (hlen: ¬(List.length as == 0 && List.length bs == 0) = true): List.length (evens (a :: as)) + List.length (evens (b :: bs)) < Nat.succ (List.length as) + Nat.succ (List.length bs) := by
    unfold evens;
    simp at hlen;
    rw [List.length_cons, List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _];
    ring_nf;
    cases as with
    | nil => cases bs with
      | nil => simp at hlen;
      | cons bhead btail => unfold odds; simp; linarith [@len_evens_le btail];
    | cons ahead atail =>
      rw [add_comm, add_comm (2 + List.length (ahead :: atail)) (List.length bs)]
      refine add_lt_add_of_le_of_lt (@len_odds_le bs) ?h; unfold odds; simp; linarith [@len_evens_le atail];

lemma bmerge_term2 (x y: Nat) (xs ys: List Nat) : List.length (odds (x :: xs)) + List.length (odds (y :: ys)) < Nat.succ (List.length xs) + Nat.succ (List.length ys) := by
  unfold odds;
  exact add_lt_add_of_lt_of_lt (Nat.lt_succ_of_le (@len_evens_le xs)) (Nat.lt_succ_of_le (@len_evens_le ys))

def bmerge : List Nat → List Nat → List Nat
| [], bs => bs -- I changed this from TIP. I don't believe this case is ever hit, though.
| as, [] => as
| x::xs, y::ys =>
  if hlen: xs.length == 0 && ys.length == 0 then sort2 x y else
  have _h := bmerge_term x y xs ys hlen;
  have _h2 := bmerge_term2 x y xs ys;
  stitch (bmerge (evens (x::xs)) (evens (y::ys))) (bmerge (odds (x::xs)) (odds (y::ys)))
termination_by xs ys => xs.length + ys.length

lemma bsort_term1 (x y: Nat) (xs: List Nat): List.length (evens (x :: y :: xs)) < Nat.succ (Nat.succ (List.length xs)) := by
  unfold evens; unfold odds;
  rw [List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _];
  simp;
  exact Nat.lt_succ_of_le (@len_evens_le xs);

lemma bsort_term2 (x y: Nat) (xs: List Nat): List.length (odds (x :: y :: xs)) < Nat.succ (Nat.succ (List.length xs)) := by
  unfold odds; unfold evens;
  rw [List.length_cons, Nat.succ_eq_add_one _, Nat.succ_eq_add_one _];
  simp;
  exact Nat.lt_succ_of_le (@len_odds_le xs);

def bsort : List Nat → List Nat
| [] => []
| [x] => [x]
| x::y::xs =>
  have _h := bsort_term1 x y xs
  have _h2 := bsort_term2 x y xs
  bmerge (bsort (evens (x::y::xs))) (bsort (odds (x::y::xs)))
termination_by xs => xs.length

def prop_BSortSorts (xs: List Nat) := ordered (bsort xs) == true
def prop_BSortCount (x: Nat) (xs: List Nat) := count x (bsort xs) == count x xs
def prop_BSortPermutes (xs: List Nat) := isPermutation (bsort xs) xs == true
def prop_BSortIsSort (xs: List Nat) := bsort xs == isort xs

def filter : List Nat → (Nat → Bool) → List Nat
| [], _f => []
| x::xs, f => if f x then x::(filter xs f) else (filter xs f)

lemma filter_len_le {f: Nat → Bool} {xs: List Nat}: (filter xs f).length <= xs.length := by
  generalize hxsl: xs.length = xsl
  induction xsl generalizing xs with
  | zero => rw [List.length_eq_zero] at hxsl; rw [hxsl]; unfold filter; simp;
  | succ n ih =>
    cases xs with
    | nil => unfold filter; simp;
    | cons head tail =>
      rw [List.length_cons] at hxsl; simp at hxsl;
      unfold filter; split_ifs with h1;
      case pos;
        rw [List.length_cons];
        exact Nat.pred_le_iff.mp (ih hxsl)
      case neg;
        exact Nat.le.step (ih hxsl)


lemma qsort_term (x:Nat) (xs: List Nat) : List.length (filter xs fun y => decide (y ≤ x)) < Nat.succ (List.length xs) := by
  exact Nat.lt_succ_of_le (filter_len_le);

lemma qsort_term2 (x:Nat) (xs: List Nat) : List.length (filter xs fun y => decide (y > x)) < Nat.succ (List.length xs) := by
  exact Nat.lt_succ_of_le (filter_len_le);

def qsort : List Nat → List Nat
| [] => []
| x::xs =>
  have _h:= qsort_term x xs
  have _h2:= qsort_term2 x xs
  (qsort (filter xs (fun y => y <= x))) ++ [x] ++ (qsort (filter xs (fun y => y > x)))
termination_by xs => xs.length

def prop_QSortSorts (xs: List Nat) := ordered (qsort xs) == true
def prop_QSortCount (x: Nat) (xs: List Nat) := count x (qsort xs) == count x xs
def prop_QSortPermutes (xs: List Nat) := isPermutation (qsort xs) xs == true
def prop_QSortIsSort (xs: List Nat) := qsort xs == isort xs

def minimum : Nat → List Nat → Nat
| x, [] => x
| x, y::ys => if y <= x then minimum y ys else minimum x ys

lemma min_in_list : minimum x xs ∈ (x::xs) := by
  induction xs generalizing x with
  | nil => unfold minimum; simp;
  | cons head tail ih =>
    unfold minimum; split_ifs with h1;
    case pos;
      rw [List.mem_cons]; right; exact ih;
    case neg;
      rw [List.mem_cons];
      cases (List.mem_cons.1 (@ih x)) with
      | inl h2 => left; exact h2;
      | inr h2 => right; rw [List.mem_cons]; right; exact h2;

lemma delete_len_eq {x: Nat} {xs: List Nat} (h: x ∈ xs): (deleteFirst x xs).length + 1 = xs.length := by
  generalize hxsl: xs.length = xsl
  induction xsl generalizing xs with
  | zero => rw [List.length_eq_zero] at hxsl; simp [hxsl] at h;
  | succ n ih =>
    cases xs with
    | nil => simp at hxsl;
    | cons head tail =>
      unfold deleteFirst;
      split_ifs with h1;
      case pos;
        simp at hxsl;
        simp [hxsl];
      case neg;
        rw [List.mem_cons] at h;
        simp at h1;
        simp at hxsl;
        simp;
        exact ih ((or_iff_right h1).1 h) hxsl;

-- Selection sort, using a total minimum function
def ssort : List Nat → List Nat
| [] => []
| x::xs =>
  let m := minimum x xs
  have _h: List.length (deleteFirst (minimum x xs) (x :: xs)) < Nat.succ (List.length xs) := by
    have tmp := delete_len_eq (@min_in_list x xs)
    simp at tmp;
    simp [tmp];
  m :: ssort (deleteFirst m (x::xs))
termination_by xs => xs.length

def prop_SSortSorts (xs: List Nat) := ordered (ssort xs) == true
def prop_SSortCount (x: Nat) (xs: List Nat) := count x (ssort xs) == count x xs
def prop_SSortPermutes (xs: List Nat) := isPermutation (ssort xs) xs == true
def prop_SSortIsSort (xs: List Nat) := ssort xs == isort xs


inductive MyTree where
| nil : MyTree
| node : MyTree → Nat → MyTree → MyTree

def add : Nat → MyTree → MyTree
| x, .nil => .node .nil x .nil
| x, .node p y q => if x <= y then .node (add x p) y q else .node p y (add x q)

def toTree : List Nat → MyTree
| [] => .nil
| x::xs => add x (toTree xs)

def flatten : MyTree → List Nat → List Nat
| .nil, ys => ys
| .node p x q, ys => flatten p (x :: flatten q ys)

def tsort : List Nat → List Nat
| xs => flatten (toTree xs) []

def prop_TSortSorts (xs: List Nat) := ordered (tsort xs) == true
def prop_TSortCount (x: Nat) (xs: List Nat) := count x (tsort xs) == count x xs
def prop_TSortPermutes (xs: List Nat) := isPermutation (tsort xs) xs == true
def prop_TSortIsSort (xs: List Nat) := tsort xs == isort xs

def splitAt : Nat → List Nat → (List Nat × List Nat)
| _n, [] => ([], [])
| 0, xs => ([], xs)
| n + 1, x::xs => match splitAt n xs with
  | (l1, l2) => (x::l1, l2)

def reverse : List Nat → List Nat
| [] => []
| x::xs => (reverse xs) ++ [x]

lemma len_rev_eq_len {l: List Nat} : (reverse l).length = l.length := by
  induction l with
  | nil => simp [reverse]
  | cons head tail ih => unfold reverse; simp [ih];

lemma splitAt_len_le {xs: List Nat}: (splitAt n xs).2.length ≤ xs.length := by
  induction xs generalizing n with
  | nil => unfold splitAt; simp;
  | cons head tail ih =>
    cases n with
    | zero => unfold splitAt; simp;
    | succ nm1 => unfold splitAt; simp; apply Nat.le.step; exact ih;

lemma splitAt_second_len_lt (n: Nat): (splitAt n.succ (x::xs)).2.length < (x::xs).length := by
  unfold splitAt;
  simp;
  calc List.length (splitAt n xs).2 ≤ (List.length xs) := splitAt_len_le
       _                          < Nat.succ (List.length xs) := Nat.lt_succ_self _

lemma splitAt_second_len_lt' {xs: List Nat} (n: Nat) (hlen: xs.length > 0): (splitAt n.succ xs).2.length < xs.length := by
  cases xs with
  | nil => simp at hlen;
  | cons x xs => exact splitAt_second_len_lt _;

lemma splitAt_second_len_lt'' {xs: List Nat} (hn: n > 0) (hlen: xs.length > 0) (hlen': xl = xs.length): (splitAt n xs).2.length < xl := by
  cases n with
  | zero => simp at hn;
  | succ nm1 => rw [hlen']; exact splitAt_second_len_lt' _ hlen;

lemma splitAt_sum_preserves_len (n: Nat) (xs: List Nat) (hspl: spl = splitAt n xs): (spl.1.length + spl.2.length = xs.length) := by
  induction xs generalizing n spl with
  | nil => simp [splitAt] at hspl; simp [hspl];
  | cons head tail ih => cases n with
    | zero => simp [splitAt] at hspl; simp [hspl];
    | succ nm1 =>
      simp [splitAt] at hspl;
      simp [hspl]
      rw [Nat.succ_add];
      apply Order.succ_eq_succ_iff.2
      exact ih nm1 (by rfl);

--set_option maxHeartbeats 9999999

def stoogesort (xs : {xs : List Nat // xs.length = n}) : {ys: List Nat // ys.length = n} := match xs with
| ⟨[], h⟩ => ⟨[], h⟩
| ⟨[x], h⟩ => ⟨[x], h⟩
| ⟨[x, y], h⟩ => if x <= y then ⟨[x, y], h⟩ else ⟨[y, x], by simp [←h]⟩
| ⟨x1::x2::x3::xs, hlen⟩ =>
  let yzs1 := splitAt ((x1::x2::x3::xs).length/3) (reverse (x1::x2::x3::xs))
  let ⟨tmp2, hlen2⟩ := (@stoogesort yzs1.2.length ⟨yzs1.2, by rfl⟩)
  let s1s2a := tmp2 ++ (reverse yzs1.1)
  let yzs2 := splitAt (s1s2a.length/3) s1s2a
  let ⟨tmp3, hlen3⟩ := (@stoogesort yzs2.2.length ⟨yzs2.2, by rfl⟩)
  let s1s1 := yzs2.1 ++ tmp3
  let yzs3 := splitAt (s1s1.length/3) (reverse s1s1)
  let ⟨tmp4, hlen4⟩ := (@stoogesort yzs3.2.length ⟨yzs3.2, by rfl⟩)
  ⟨tmp4 ++ (reverse yzs3.1), by
    simp [hlen4, len_rev_eq_len];
    rw [add_comm];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs3), len_rev_eq_len];
    unfold_let s1s1
    simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
    unfold_let s1s2a
    simp [hlen2, len_rev_eq_len];
    rw [add_comm];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs1), len_rev_eq_len, hlen]
    ⟩
termination_by match xs with | ⟨lst, _h⟩ => lst.length
decreasing_by
  simp_wf
  apply splitAt_second_len_lt''
    (by simp [Nat.succ_eq_add_one, Nat.add_assoc])
    (by simp [len_rev_eq_len, Nat.succ_eq_add_one, Nat.add_assoc])
    (by simp [len_rev_eq_len, hlen])
  -- second call termination
  simp_wf
  suffices hyzs2 : (splitAt (List.length s1s2a / 3) s1s2a).2.length < n
  rw [List.length_append] at hyzs2
  exact hyzs2;
  unfold_let s1s2a
  suffices hyzs1 : List.length (tmp2 ++ reverse yzs1.1) = List.length xs + 3
  exact splitAt_second_len_lt'' (by simp [hyzs1]) (by simp [hyzs1]) (by simp [hyzs1, ←hlen])
  simp [hlen2, len_rev_eq_len, Nat.add_comm, splitAt_sum_preserves_len _ _ (Eq.refl yzs1)]
  ring_nf
  --
  simp_wf
  suffices hyzs3 : (splitAt (List.length s1s1 / 3) (reverse s1s1)).2.length < n
  unfold_let s1s1 yzs2 s1s2a yzs1 at hyzs3
  simp [List.length_append] at hyzs3;
  exact hyzs3;
  suffices hs1s1: s1s1.length = xs.length + 3
  exact splitAt_second_len_lt'' (by simp [hs1s1]) (by simp [len_rev_eq_len, hs1s1]) (by simp [len_rev_eq_len, hs1s1, ←hlen])
  unfold_let s1s1
  simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
  unfold_let s1s2a
  simp [hlen2, len_rev_eq_len, Nat.add_comm, splitAt_sum_preserves_len _ _ (Eq.refl yzs1)]
  ring_nf


def stoogesort' (xs: List Nat) := stoogesort ⟨xs, Eq.refl xs.length⟩

def prop_StoogeSortSorts (xs: List Nat) := ordered (stoogesort' xs) == true
def prop_StoogeSortCount (x: Nat) (xs: List Nat) := count x (stoogesort' xs) == count x xs
def prop_StoogeSortPermutes (xs: List Nat) := isPermutation (stoogesort' xs) xs == true
def prop_StoogeSortIsSort (xs: List Nat) := stoogesort' xs == isort xs


lemma splitAt_first_len_lt {xs: List Nat} (hn: n < xl) (hlen': xl = xs.length): (splitAt n xs).1.length < xl := by
  suffices heq : (splitAt n xs).1.length = n
  simp [heq, hn]
  induction xs generalizing n xl with
  | nil => simp [hlen'] at hn;
  | cons head tail ih =>
    cases n with
    | zero => simp [splitAt];
    | succ nm1 =>
      simp [splitAt];
      exact @ih nm1 tail.length (by simp [hlen'] at hn; exact hn) rfl

lemma twon_lt (n: Nat): (2*n.succ.succ.succ + 1)/ 3 < n.succ.succ.succ := by
  simp [Nat.succ_eq_add_one];
  ring_nf;
  rw [Nat.div_lt_iff_lt_mul (by simp)];
  ring_nf;
  --if linarith couldn't show this, it would be pretty useless
  linarith;

def stoogesort2 (xs : {xs : List Nat // xs.length = n}) : {ys: List Nat // ys.length = n} := match xs with
| ⟨[], h⟩ => ⟨[], h⟩
| ⟨[x], h⟩ => ⟨[x], h⟩
| ⟨[x, y], h⟩ => if x <= y then ⟨[x, y], h⟩ else ⟨[y, x], by simp [←h]⟩
| ⟨x1::x2::x3::xs, hlen⟩ =>
  let yzs1 := splitAt ((2*(x1::x2::x3::xs).length + 1) / 3) (x1::x2::x3::xs)
  let ⟨tmp2, hlen2⟩ := @stoogesort2 yzs1.1.length ⟨yzs1.1, by rfl⟩
  let s2s2a := tmp2 ++ yzs1.2
  let yzs2 := splitAt (s2s2a.length / 3) s2s2a
  let ⟨tmp3, hlen3⟩ := @stoogesort2 yzs2.2.length ⟨yzs2.2, by rfl⟩
  let s2s1 := yzs2.1 ++ tmp3
  let yzs3 := splitAt ((2*s2s1.length + 1) / 3) s2s1
  let ⟨tmp4, hlen4⟩ := @stoogesort2 yzs3.1.length ⟨yzs3.1, by rfl⟩
  ⟨tmp4 ++ yzs3.2, by
    simp [hlen4];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs3), len_rev_eq_len];
    unfold_let s2s1
    simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
    unfold_let s2s2a
    simp [hlen2];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs1), hlen]
    ⟩
termination_by match xs with | ⟨lst, _h⟩ => lst.length
decreasing_by
  simp_wf;
  simp at hlen;
  rw [← hlen]
  apply splitAt_first_len_lt (twon_lt _) (by simp)
  --
  simp_wf;
  suffices hyzs2 : yzs2.2.length < n
  unfold_let yzs2 at hyzs2
  rw [List.length_append] at hyzs2
  exact hyzs2;
  unfold_let yzs2
  suffices hs2s2a : s2s2a.length = n
  rw [hs2s2a, ← hlen]
  apply splitAt_second_len_lt'' (by simp [Nat.succ_eq_add_one, Nat.add_assoc]) (by simp [hs2s2a, ←hlen]) (by simp [hs2s2a, ←hlen])
  unfold_let s2s2a
  simp [hlen2, splitAt_sum_preserves_len _ _ (Eq.refl yzs1), hlen]
  --
  simp_wf;
  suffices hdone: yzs3.1.length < n
  unfold_let yzs3 s2s1 yzs2 s2s2a yzs1 at hdone
  simp [List.length_append] at hdone;
  exact hdone;
  unfold_let yzs3
  suffices hs2s1: s2s1.length = xs.length.succ.succ.succ
  refine splitAt_first_len_lt (by simp [hs2s1, ← hlen]; exact twon_lt _) (by simp [hs2s1, ← hlen])
  --
  unfold_let s2s1
  simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
  unfold_let s2s2a
  simp [hlen2, len_rev_eq_len, Nat.add_comm, splitAt_sum_preserves_len _ _ (Eq.refl yzs1)]
  ring_nf

def stoogesort2' (xs: List Nat) := stoogesort2 ⟨xs, by rfl⟩

def prop_StoogeSort2Sorts (xs: List Nat) := ordered (stoogesort2' xs) == true
def prop_StoogeSort2Count (x: Nat) (xs: List Nat) := count x (stoogesort2' xs) == count x xs
def prop_StoogeSort2Permutes (xs: List Nat) := isPermutation (stoogesort2' xs) xs == true
def prop_StoogeSort2IsSort (xs: List Nat) := stoogesort2' xs == isort xs

lemma third_eq_div_3 : (x/3) = third x := by
  induction x using Nat.strongInductionOn with
  | ind x ih =>
  unfold third
  match x with
  | 0 => simp;
  | 1 => simp;
  | 2 => simp;
  | n + 3 => simp [Nat.succ_eq_add_one]; ring_nf; linarith [ih n (by linarith)]


def nstoogesort (xs : {xs : List Nat // xs.length = n}) : {ys: List Nat // ys.length = n} := match xs with
| ⟨[], h⟩ => ⟨[], h⟩
| ⟨[x], h⟩ => ⟨[x], h⟩
| ⟨[x, y], h⟩ => if x <= y then ⟨[x, y], h⟩ else ⟨[y, x], by simp [←h]⟩
| ⟨x1::x2::x3::xs, hlen⟩ =>
  let yzs1 := splitAt (third (x1::x2::x3::xs).length) (reverse (x1::x2::x3::xs))
  let ⟨tmp2, hlen2⟩ := (@nstoogesort yzs1.2.length ⟨yzs1.2, by rfl⟩)
  let s1s2a := tmp2 ++ (reverse yzs1.1)
  let yzs2 := splitAt (third s1s2a.length) s1s2a
  let ⟨tmp3, hlen3⟩ := (@nstoogesort yzs2.2.length ⟨yzs2.2, by rfl⟩)
  let s1s1 := yzs2.1 ++ tmp3
  let yzs3 := splitAt (third s1s1.length) (reverse s1s1)
  let ⟨tmp4, hlen4⟩ := (@nstoogesort yzs3.2.length ⟨yzs3.2, by rfl⟩)
  ⟨tmp4 ++ (reverse yzs3.1), by
    simp [hlen4, len_rev_eq_len];
    rw [add_comm];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs3), len_rev_eq_len];
    unfold_let s1s1
    simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
    unfold_let s1s2a
    simp [hlen2, len_rev_eq_len];
    rw [add_comm];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs1), len_rev_eq_len, hlen]
    ⟩
termination_by match xs with | ⟨lst, _h⟩ => lst.length
decreasing_by
  simp_wf
  apply splitAt_second_len_lt''
    (by simp [←third_eq_div_3, Nat.succ_eq_add_one, Nat.add_assoc])
    (by simp [len_rev_eq_len, Nat.succ_eq_add_one, Nat.add_assoc])
    (by simp [len_rev_eq_len, hlen])
  -- second call termination
  simp_wf
  suffices hyzs2 : (splitAt (List.length s1s2a / 3) s1s2a).2.length < n
  rw [List.length_append, third_eq_div_3] at hyzs2
  exact hyzs2;
  unfold_let s1s2a
  suffices hyzs1 : List.length (tmp2 ++ reverse yzs1.1) = List.length xs + 3
  exact splitAt_second_len_lt'' (by simp [hyzs1]) (by simp [hyzs1]) (by simp [hyzs1, ←hlen])
  simp [hlen2, len_rev_eq_len, Nat.add_comm, splitAt_sum_preserves_len _ _ (Eq.refl yzs1)]
  ring_nf
  --
  simp_wf
  suffices hyzs3 : (splitAt (List.length s1s1 / 3) (reverse s1s1)).2.length < n
  unfold_let s1s1 yzs2 s1s2a yzs1 at hyzs3
  simp [List.length_append, third_eq_div_3] at hyzs3;
  exact hyzs3;
  suffices hs1s1: s1s1.length = xs.length + 3
  exact splitAt_second_len_lt'' (by simp [hs1s1]) (by simp [len_rev_eq_len, hs1s1]) (by simp [len_rev_eq_len, hs1s1, ←hlen])
  unfold_let s1s1
  simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
  unfold_let s1s2a
  simp [hlen2, len_rev_eq_len, Nat.add_comm, splitAt_sum_preserves_len _ _ (Eq.refl yzs1)]
  ring_nf

def nstoogesort' (xs: List Nat) := nstoogesort ⟨xs, (by rfl)⟩

def prop_NStoogeSortSorts (xs: List Nat) := ordered (nstoogesort' xs) == true
def prop_NStoogeSortCount (x: Nat) (xs: List Nat) := count x (nstoogesort' xs) == count x xs
def prop_NStoogeSortPermutes (xs: List Nat) := isPermutation (nstoogesort' xs) xs == true
def prop_NStoogeSortIsSort (xs: List Nat) := nstoogesort' xs == isort xs

lemma twon_lt' (n: Nat): twoThirds (n.succ.succ.succ) < n.succ.succ.succ := by
  induction n using Nat.strongInductionOn with
  | ind x ih =>
  unfold twoThirds
  match x with
  | 0 => simp [twoThirds];
  | 1 => simp [twoThirds];
  | 2 => simp [twoThirds];
  | x + 3 => linarith [ih x (by linarith)]

def nstoogesort2 (xs : {xs : List Nat // xs.length = n}) : {ys: List Nat // ys.length = n} := match xs with
| ⟨[], h⟩ => ⟨[], h⟩
| ⟨[x], h⟩ => ⟨[x], h⟩
| ⟨[x, y], h⟩ => if x <= y then ⟨[x, y], h⟩ else ⟨[y, x], by simp [←h]⟩
| ⟨x1::x2::x3::xs, hlen⟩ =>
  let yzs1 := splitAt (twoThirds (x1::x2::x3::xs).length) (x1::x2::x3::xs)
  let ⟨tmp2, hlen2⟩ := @nstoogesort2 yzs1.1.length ⟨yzs1.1, by rfl⟩
  let s2s2a := tmp2 ++ yzs1.2
  let yzs2 := splitAt (third s2s2a.length) s2s2a
  let ⟨tmp3, hlen3⟩ := @nstoogesort2 yzs2.2.length ⟨yzs2.2, by rfl⟩
  let s2s1 := yzs2.1 ++ tmp3
  let yzs3 := splitAt (twoThirds s2s1.length) s2s1
  let ⟨tmp4, hlen4⟩ := @nstoogesort2 yzs3.1.length ⟨yzs3.1, by rfl⟩
  ⟨tmp4 ++ yzs3.2, by
    simp [hlen4];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs3), len_rev_eq_len];
    unfold_let s2s1
    simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
    unfold_let s2s2a
    simp [hlen2];
    simp [splitAt_sum_preserves_len _ _ (Eq.refl yzs1), hlen]
    ⟩
termination_by match xs with | ⟨lst, _h⟩ => lst.length
decreasing_by
  simp_wf;
  simp at hlen;
  rw [← hlen]
  apply splitAt_first_len_lt (twon_lt' _) (by simp)
  --
  simp_wf;
  suffices hyzs2 : yzs2.2.length < n
  unfold_let yzs2 at hyzs2
  rw [List.length_append] at hyzs2
  exact hyzs2;
  unfold_let yzs2
  suffices hs2s2a : s2s2a.length = n
  rw [hs2s2a, ← hlen]
  apply splitAt_second_len_lt'' (by simp [←third_eq_div_3, Nat.succ_eq_add_one, Nat.add_assoc]) (by simp [hs2s2a, ←hlen]) (by simp [hs2s2a, ←hlen])
  unfold_let s2s2a
  simp [hlen2, splitAt_sum_preserves_len _ _ (Eq.refl yzs1), hlen]
  --
  simp_wf;
  suffices hdone: yzs3.1.length < n
  unfold_let yzs3 s2s1 yzs2 s2s2a yzs1 at hdone
  simp [List.length_append] at hdone;
  exact hdone;
  unfold_let yzs3
  suffices hs2s1: s2s1.length = xs.length.succ.succ.succ
  refine splitAt_first_len_lt (by simp [hs2s1, ← hlen]; exact twon_lt' _) (by simp [hs2s1, ← hlen])
  --
  unfold_let s2s1
  simp [hlen3, splitAt_sum_preserves_len _ _ (Eq.refl yzs2)]
  unfold_let s2s2a
  simp [hlen2, len_rev_eq_len, Nat.add_comm, splitAt_sum_preserves_len _ _ (Eq.refl yzs1)]
  ring_nf

def nstoogesort2' (xs: List Nat) := nstoogesort ⟨xs, (by rfl)⟩

def prop_NStoogeSort2Sorts (xs: List Nat) := ordered (nstoogesort2' xs) == true
def prop_NStoogeSort2Count (x: Nat) (xs: List Nat) := count x (nstoogesort2' xs) == count x xs
def prop_NStoogeSort2Permutes (xs: List Nat) := isPermutation (nstoogesort2' xs) xs == true
def prop_NStoogeSort2IsSort (xs: List Nat) := nstoogesort2' xs == isort xs

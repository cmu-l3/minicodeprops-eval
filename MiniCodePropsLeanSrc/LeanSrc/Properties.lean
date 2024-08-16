import Mathlib
import LeanSrc.Definitions

def hello := "world"

-- Scoring guidelines:
-- anything that doesn't involve programs (i.e. list operations) can be at max a 3/5

-- besides that, 5/5 is for properties that don't directly follow from the program definition, and often
-- involve multiple programs. 4/5 is generally only a step beyond following from definition. 3/5 is a
-- statement about programs thats trivial, or a math statement that's nontrivial. 2 and 1 follow the
-- decreases in interestingness for math that we saw for 4 and 3 for programs.

-- take returns a list with the first n elements of the input list
-- drop deletes the first n elements of the input list

-- Score: 5/5: concatenating take(n) and drop(n) gives you back the original list
def prop_01 (n: Nat) (xs: List α) :=
 List.take n xs ++ List.drop n xs = xs

-- Score: 5/5: the sum of the number of times you see n in two lists is equal to the number of times you see n in the concatenation of those lists
def prop_02 (n: Nat) (xs: List Nat) (ys: List Nat) :=
 List.count n xs + List.count n ys = List.count n (xs ++ ys)

-- Score: 4/5: you at most as many n's in a list as when you concatenate the list with another one.
def prop_03 (n: Nat) (xs: List Nat) (ys: List Nat) :=
 List.count n xs <= List.count n (xs ++ ys)

-- Score: 3/5: adding an n to a list means the count of n's in that list goes up by 1
def prop_04 (n: Nat) (xs: List Nat) :=
  (List.count n xs).succ = List.count n (n :: xs)

-- Score: 4/5: obfuscated version of prop_04
def prop_05 (n: Nat) (x: Nat) (xs: List Nat) :=
 (n = x) →  (List.count n xs).succ = List.count n (x :: xs)

-- Score: 2/5: in natural numbers, subtracting something bigger than n from n gives you 0
def prop_06 (n: Nat) (m: Nat) :=
 (n - (n + m) = 0)

-- Score: 1/5: adding two things and subtracting the first gives you the second
def prop_07 (n: Nat) (m: Nat) :=
 ((n + m) - n = m)

-- Score: 3/5:  (k+m) - (k+n) = m - n. At least this shouldn't be trivial, but it isn't program verification.
def prop_08 (k:Nat) (m: Nat) (n: Nat) :=
  ((k + m) - (k + n) = m - n)

-- Score: 2/5: distribute and associate negatives
def prop_09 (i: Nat) (j: Nat) (k: Nat) :=
  ((i - j) - k = i - (j + k))

-- score: 1/5: subtract self is zero
def prop_10 (m: Nat) :=
 (m - m = 0)

-- score: 3/5: dropping nothing gives the original list
def prop_11 (xs: List α) :=
   (List.drop 0 xs = xs)

-- score: 5/5: drop can happen before or after map with the same result
def prop_12 (n: Nat) (f: α → α) (xs: List α) :=
   (List.drop n (List.map f xs) = List.map f (List.drop n xs))

-- score: 5/5: dropping n+1 from a list with an extra value up front is the same as dropping n from the original list
def prop_13 (n: Nat) (x: α) (xs: List α) :=
 (List.drop n.succ (x :: xs) = List.drop n xs)

-- score: 5/5: filter then append is the same as append then filter
def prop_14 (p: α → Bool) (xs: List α) (ys: List α) :=
  (List.filter p (xs ++ ys) = (List.filter p xs) ++ (List.filter p ys))

-- score: 5/5: length of custom ordered insert of x is one more than the original length
def prop_15 (x: Nat) (xs: List Nat) :=
  (List.length (ins x xs)) = (List.length xs).succ

-- score: 5/5: custom last element of single element list is that element.
def prop_16 (x: Nat) (xs: List Nat) :=
 xs = [] →  last (x::xs) = x

-- score: 1/5: if a nat is at most 0 then it's zero
def prop_17 (n: Nat) :=
  n <= 0 ↔ n = 0

-- score: 2/5: even if you add something, i is less than i+1
def prop_18 i (m: Nat) :=
   i < (i + m).succ

-- score: 5/5: the length of a dropped-n list is the original list's length minus n.
def prop_19 (n: Nat) (xs: List Nat) :=
 (List.length (List.drop n xs) = List.length xs - n)

-- This property is the same as prod #48
-- score: 5/5: The length of a custom insertion sorted list is equal to the list's original length
def prop_20 (xs: List Nat) :=
  (List.length (sort xs) = List.length xs)

-- score: 1/5: A number is less than or equal to the number plus something
def prop_21 (n: Nat) (m: Nat) :=
  n <= (n + m)

-- score: 2/5: the max operator associates
def prop_22 (a: Nat) (b: Nat) (c: Nat) :=
  (max (max a b) c = max a (max b c))

-- score: 1/5: the max operator commutes
def prop_23 (a: Nat) (b: Nat) :=
  (max a b = max b a)

-- score: 2/5: the max of two numbers is geq the other one
def prop_24 (a: Nat) (b: Nat) :=
 (((max a b) = a) ↔ b <= a)

-- score: 2/5: same as prop_24 but the max is the second number
def prop_25 (a: Nat) (b: Nat) :=
  (((max a b) = b) ↔ a <= b)

-- score: 4/5: If x is in a list, its in that list concatenated with another list
def prop_26 (x: α) (xs: List α) (ys: List α) :=
  x ∈ xs →  x ∈ (xs ++ ys)

-- score: 4/5: If x is in a list, its in another list concatenated with that list
def prop_27 (x: α) (xs: List α) (ys: List α) :=
 x ∈ ys → x ∈ (xs ++ ys)

-- score: 4/5: x is in a list concatenated with the singleton list containing x
def prop_28 (x: α) (xs: List α) :=
  x ∈ (xs ++ [x])

-- score: 5/5: x is in the result of custom inserting x into xs at the end when xs doesn't already contain x
def prop_29 (x: Nat) (xs: List Nat) :=
  x ∈ ins1 x xs

-- score: 5/5: x is in the result of custom inserting x into xs before the first location where an element in xs is greater than x
def prop_30 (x: Nat) (xs: List Nat) :=
  x ∈ ins x xs

-- score: 2/5: the min operator associates
def prop_31 (a: Nat) (b: Nat) (c: Nat) :=
  min (min a b) c = min a (min b c)

-- score: 1/5: the min operator commutes
def prop_32 (a: Nat) (b: Nat) :=
  min a b = min b a

-- score: 2/5: Iff the min of two numbers is the first one, the first is leq the second
def prop_33 (a: Nat) (b: Nat) :=
  min a b = a ↔ a <= b

-- score: 2/5: Iff the min of two numbers is the second one, the second is leq the first
def prop_34 (a: Nat) (b: Nat) :=
  min a b = b ↔ b <= a

-- score: 5/5: Dropping elements until a custom function that returns false returns false yields the original list.
def prop_35 (xs: List α) :=
  dropWhile (fun _ => False) xs = xs

-- score: 5/5: keeping elements while a custom function that returns true returns true yields the original list.
def prop_36 (xs: List α) :=
  takeWhile (fun _ => True) xs = xs

-- score: 5/5: an element x is not a member of the list resulting from calling a custom function that deletes x from a list.
def prop_37 (x: Nat) (xs: List Nat) :=
  not (x ∈ delete x xs)

-- score: 4/5: The number of occurences of a number n in a list with a single n appended is one more than the number of times n appears in the original list.
def prop_38 (n: Nat) (xs: List Nat) :=
  List.count n (xs ++ [n]) = (List.count n xs).succ

-- score: 4/5: the number of times n appears in a list with first element x and remaining elements xs is equal to the number of
def prop_39 (n: Nat) (x: Nat) (xs: List Nat) :=
  List.count n [x] + List.count n xs = List.count n (x::xs)

-- score: 3/5: taking no elements from a list results in an empty list
def prop_40 (xs: List α) :=
 (List.take 0 xs = [])

--score: 5/5: mapping a function over a list and takig the first n elements is the same as performing those operations in the oppositie order
def prop_41 (n: Nat) (f: α → α) (xs: List α) :=
  (List.take n (List.map f xs) = List.map f (List.take n xs))

--score: 4/5: taking n+1 elements from a list is the same as cons-ing the first element of the list to the result of taking n from the rest of the list
def prop_42 (n: Nat) (x: α) (xs: List α) :=
  (List.take n.succ (x::xs) = x :: (List.take n xs))

-- score: 5/5: custom taking elements while a predicate is true and appending to custom dropping while a predicate is true results in the original list
def prop_43 (p: Nat → Bool) (xs: List Nat) :=
  (takeWhile p xs ++ dropWhile p xs = xs)

-- score: 5/5: the custom zip' function is the same as the custom zipconcat function with the first list split into first and rest as the first two arguments
def prop_44 (x: α) (xs: List α) (ys: List β) :=
  zip' (x::xs) ys = zipConcat x xs ys

-- score: 4/5: the recursive definition of the custom zip' function
def prop_45 (x: α) (y: β) (xs: List α) (ys: List β) :=
  zip' (x::xs) (y::ys) = (x, y) :: zip' xs ys

-- score: 5/5: custom zipping an empty list with another list yields the empty list
def prop_46 {α β: Type} (xs: List β) :=
  zip' ([]: List α) xs = []

-- score: 5/5: The custom height of a custom binary tree is the same as the custom height of that tree when custom mirrored
def prop_47 (a: MyTree α) :=
  (height' (mirror a) = height' a)

-- score: 5/5: If a list is not custom empty, append all but the custom last element with the custom last element recovers the original list
def prop_48 (xs: List Nat) :=
  not (null xs) → butlast xs ++ [last xs] = xs

-- score: 4/5: The recursive definition of the custom butlastConcat function
def prop_49 (xs: List Nat) (ys: List Nat) :=
  (butlast (xs ++ ys) = butlastConcat xs ys)

-- score: 5/5: The custom butlast function is equivalent to taking one less than the length of the list
def prop_50 (xs: List α) :=
  (butlast xs = List.take (List.length xs - 1) xs)

-- score: 5/5: calling custom butlast on a list with a new element appended returns the original list
def prop_51 (xs: List α) (x: α) :=
  (butlast (xs ++ [x]) = xs)

-- score: 5/5: The number of times a value appears in a list does not change when the list is reversed
def prop_52 (n: Nat) xs :=
  (List.count n xs = List.count n (List.reverse xs))

-- This property is the same as prod #50
-- score: 5/5: The number of times a value appears in a list does not change when the list is custom sorted
def prop_53 (n: Nat) xs :=
  (List.count n xs = List.count n (sort xs))

-- score: 2/5: adding a number and then subtracting it recovers the original number
def prop_54 (n: Nat) (m: Nat) :=
  ((m + n) - n = m)

-- score: 5/5: Dropping n from appending two lists is equal to appending dropping n from the first list and dropping n minus the length of the first list from the second list.
def prop_55 (n: Nat) (xs: List α) (ys: List α) :=
  (List.drop n (xs ++ ys) = List.drop n xs ++ List.drop (n - List.length xs) ys)

-- score: 5/5: Dropping m elements from a list and then dropping n elements from the list is the same as dropping m+n elements from the list
def prop_56 (n: Nat) (m: Nat) (xs: List α) :=
  (List.drop n (List.drop m xs) = List.drop (n + m) xs)

-- score: 5/5: taking m from a list and then dropping n is equivalent to dropping n and then taking m minus n
def prop_57 (n: Nat) (m: Nat) (xs: List α) :=
  (List.drop n (List.take m xs) = List.take (m - n) (List.drop n xs))

-- score: 5/5: Dropping n elements from a custom zip' of two lists is equivalent to zipping both lists after dropping n from each
def prop_58 (n: Nat) (xs: List α) (ys: List β) :=
  (List.drop n (zip' xs ys) =  zip' (List.drop n xs) (List.drop n ys))

-- score: 5/5: if a list ys is empty, then getting the last element of xs appended to a list ys is equal to the last element of xs
def prop_59 (xs: List Nat) (ys: List Nat) :=
  ys = [] →  last (xs ++ ys) = last xs

-- score: 5/5: If a list ys is not custom empty, the last element of appending it to another list is the last element of ys
def prop_60 (xs: List Nat) (ys: List Nat) :=
  not (null ys) → last (xs ++ ys) = last ys

-- score: 5/5: the last of two lists appended to each other is equivalent to the custom lastOfTwo function called on the two lists
def prop_61 (xs: List Nat) (ys: List Nat) :=
  (last (xs ++ ys) = lastOfTwo xs ys)

-- score: 5/5: if a list xs is not custom empty, the last of xs with another element cons-ed to the front is equal to the last element of xs
def prop_62 (xs: List Nat) (x: Nat) :=
  not (null xs) → last (x::xs) = last xs

-- score: 5/5: if the length of a list is greater than n, the last element of the list after dropping n elements is equal to the last element of the list
def prop_63 (n: Nat) (xs: List Nat) :=
  n < List.length xs → last (List.drop n xs) = last xs

-- score: 5/5: When you append a single element to the end of a list, the last element of the result is the appended element
def prop_64 x xs :=
  (last (xs ++ [x]) = x)

-- score: 2/5: even if you add something, i is less than i+1
def prop_65 (i: Nat) (m: Nat) :=
  i < (m + i).succ

-- score: 4/5: The length of a filtered list is at most the length of the original list
def prop_66 (p: α → Bool) (xs: List α) :=
  List.length (List.filter p xs) <= List.length xs

-- score: 5/5: the length of custom all but the last element of a list is equal to the list's length minus one
def prop_67 (xs: List Nat) :=
  List.length (butlast xs) = List.length xs - 1

-- score: 5/5: The length of custom deleting all instances of n from a list is at most the length of the original list
def prop_68 (n: Nat) (xs: List Nat) :=
  List.length (delete n xs) <= List.length xs

-- score: 1/5: a number is at most the number plus any other number
def prop_69 (n: Nat) (m: Nat) :=
  n <= (m + n)

-- score: 1/5: If a number is at most another, it is at most the successor of the other
def prop_70 m (n: Nat) :=
  m <= n → m <= n.succ

-- score: 5/5: If two numbers are not equal, inserting one into a list does not change whether the other is in the list
def prop_71 (x:Nat) (y :Nat) (xs: List Nat) :=
  (x == y) = False → ((x ∈ (ins y xs)) == (x ∈ xs))

-- score: 5/5: Dropping the first i elements of a list and then reversing it is the same as reversing the list and then taking the length of the list minus i elements
def prop_72 (i: Nat) (xs: List α) :=
  (List.reverse (List.drop i xs) = List.take (List.length xs - i) (List.reverse xs))

-- score: 5/5: Filtering a list and then reversing it is the same as reversing it and then filtering it
def prop_73 (p: α → Bool) (xs: List α) :=
  (List.reverse (List.filter p xs) = List.filter p (List.reverse xs))

-- score: 5/5: Taking the first i elements of a list and then reversing it is the same as reversing the list and then dropping the length of the list minus i elements
def prop_74 (i: Nat) (xs: List α) :=
  (List.reverse (List.take i xs) = List.drop (List.length xs - i) (List.reverse xs))

-- score: 5/5: The number of times n appears in a list plus the number of times n appears in a singleton list is equal to the number of times n appears in the cons of the single element and the first list
def prop_75 (n: Nat) (m: Nat ) (xs: List Nat) :=
  (List.count n xs + List.count n [m] = List.count n (m :: xs))

-- score: 5/5: when two numbers are different, appending one to the end of a list does not change the number of times the other appears in the list
def prop_76 (n: Nat) (m: Nat) (xs: List Nat) :=
  (n == m) = False → List.count n (xs ++ [m]) = List.count n xs

-- score: 5/5: If x satisfies the custom sorted property, performing a custom sorted insert operation preserves the custom sorted property
def prop_77 (x: Nat) (xs: List Nat) :=
  sorted xs → sorted (insort x xs)

-- This property is the same as prod #14
-- score: 5/5: applying the custom sort operation to a list causes it to satify the custom sorted property
def prop_78 (xs: List Nat) :=
  sorted (sort xs)

-- score: 2/5: the result of m minus n minus k does not change when one is added to m and k
def prop_79 (m: Nat) (n: Nat) (k: Nat) :=
  ((m.succ - n) - k.succ = (m - n) - k)

-- score: 5/5: appending two lists and taking n elements is the same as  taking n elements from the first and appending n minus the length of the first list elements from the second
def prop_80 (n: Nat) (xs: List α) (ys: List α) :=
  (List.take n (xs ++ ys) = List.take n xs ++ List.take (n - List.length xs) ys)


-- score: 5/5: dropping m elements and then taking n is the same as taking n plus m elements and then dropping m
def prop_81 (n: Nat) (m: Nat) (xs: List α)  :=
  (List.take n (List.drop m xs) = List.drop m (List.take (n + m) xs))

-- score: 5/5: taking n elements from the result of custom zipping two lists is the same as taking n elements from each list and then zipping them
def prop_82 (n: Nat) (xs: List α) (ys: List β) :=
  (List.take n (zip' xs ys) = zip' (List.take n xs) (List.take n ys))

-- score: 5/5: concatenating two lists and zipping the result with a third list is the same as zipping the first list with the first list's length of elements taken from the third list appended to the result of zipping the second list with the third list but with the first length of first list elements dropped from the third list
def prop_83 (xs: List α) (ys: List α) (zs: List β) :=
  (zip' (xs ++ ys) zs =
           zip' xs (List.take (List.length xs) zs) ++ zip' ys (List.drop (List.length xs) zs))

-- score: 5/5: zipping one list with the concatenation of two more lists can be accomplished by taking the length of the second list from the first list and zipping with the second list, then concatenating with dropping the length of the second list of the first list zipped with the third list
def prop_84 (xs: List α) (ys: List β) (zs: List β) :=
  (zip' xs (ys ++ zs) =
           zip' (List.take (List.length ys) xs) ys ++ zip' (List.drop (List.length ys) xs) zs)

-- One way to prove this is to first show "Nick's lemma":
-- len xs = len ys ==> zip' xs ys ++ zip' as bs = zip' (xs ++ as) (ys ++ bs)
-- score: 5/5: if two lists are of equal length, zipping their reversals is equal to reversing the zip' of the two
def prop_85 (xs: List α) (ys: List β) :=
  (List.length xs = List.length ys) →
    (zip' (List.reverse xs) (List.reverse ys) = List.reverse (zip' xs ys))

-- score: 5/5: if x is less than y, custom inserting y into a list doesn't change whether x is in the list
def prop_86 (x: Nat) (y: Nat) (xs: List Nat) :=
  x < y → ((x ∈ (ins y xs)) == (x ∈ xs))

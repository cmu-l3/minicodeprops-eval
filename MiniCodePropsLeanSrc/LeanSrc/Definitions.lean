import Mathlib


-- We'll just use Lean's Nat
--data Nat = Z | S Nat
--  deriving (Eq,Show,Ord)

-- TODO: define Eq, Ord, show. ideally derive Eq from α
inductive MyTree (α: Type) where
| leaf : MyTree α
| node : MyTree α → α → MyTree α  →  MyTree α

--data Tree a = Leaf | Node (Tree a) a (Tree a)
--  deriving (Eq,Ord,Show)

-- we will use the Lean versions of these functions
-- Boolean functions

--not :: Bool -> Bool
--not True = False
--not False = True

--(&&) :: Bool -> Bool -> Bool
--True && True = True
--_    && _    = False

/-
-- Natural numbers

Z     == Z     = True
Z     == _     = False
(S _) == Z     = False
(S x) == (S y) = x == y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max Z     y     = y             --
max x     Z     = x
max (S x) (S y) = S (max x y)
-/

/-
-- List functions

null :: [a] -> Bool
null [] = True
null _  = False

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n == x of
    True -> delete n xs
    False -> x : (delete n xs)

len :: [a] -> Nat
len [] = Z
len (_:xs) = S (len xs)

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n == x of
    True -> True
    False -> elem n xs

drop :: Nat -> [a] -> [a]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take :: Nat -> [a] -> [a]
take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

butlast :: [a] -> [a]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insort n xs)

ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    _ -> x : (ins n xs)

ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n == x of
    True -> x : xs
    _ -> x : (ins1 n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

butlastConcat :: [a] -> [a] -> [a]
butlastConcat xs [] = butlast xs
butlastConcat xs ys = xs ++ butlast ys

lastOfTwo :: [Nat] -> [Nat] -> Nat
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

 -/

def ins: Nat → List Nat → List Nat
  | n, []  =>  [n]
  | n, x::xs => if (n < x) then n :: x :: xs else x :: (ins n xs)

def last: List Nat → Nat
  | [] => 0
  | [x] => x
  | _x::xs => (last xs)

def insort : Nat → List Nat → List Nat
  | n, [] => [n]
  | n, x::xs => if n <= x then n::x::xs else x::(insort n xs)

def sort : List Nat → List Nat
  | [] => []
  | x::xs => insort x (sort xs)

def sorted : List Nat → Bool
  | [] => True
  | [_x] => True
  | x::y::xs => and (x <= y) (sorted (y::xs))

def ins1 : Nat → List Nat → List Nat
  | n, [] => [n]
  | n, x::xs => if n == x then x::xs else x::(ins1 n xs)

def dropWhile : (α → Bool) → List α → List α
  | _, [] => []
  | p, x::xs => if p x then dropWhile p xs else x::xs

def takeWhile : (α → Bool) → List α → List α
  | _, [] => []
  | p, x::xs => if p x then x ::(takeWhile p xs) else []

def delete : Nat → List Nat → List Nat
  | _, [] => []
  | n, x::xs => if n == x then (delete n xs) else x::(delete n xs)

def zip' : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => ⟨x, y⟩ :: zip' xs ys

def zipConcat : α → List α → List β → List (α × β)
  | _, _, [] => []
  | x, xs, y::ys => ⟨x, y⟩ :: zip' xs ys

def null : List α → Bool
  | [] => True
  | _ => False

def butlast : List α → List α
  | [] => []
  | [_x] => []
  | x::xs => x::(butlast xs)

def butlastConcat : List α → List α → List α
  | xs, [] => butlast xs
  | xs, ys => xs ++ butlast ys

def lastOfTwo : List ℕ → List ℕ → ℕ
  | xs, [] => last xs
  | _, ys => last ys

def height' : MyTree α → ℕ
  | .leaf => 0
  | .node l _x r => (max (height' l) (height' r)).succ

def mirror : MyTree α → MyTree α
  | MyTree.leaf => MyTree.leaf
  | MyTree.node l x r => MyTree.node r x l

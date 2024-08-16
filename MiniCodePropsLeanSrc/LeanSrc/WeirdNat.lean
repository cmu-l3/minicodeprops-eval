import Mathlib

-- comes from original/tip2015/WeirdNat.hs

-- interestingly, if I don't define these with x+1 and y+1 in the constructor,
-- Lean can't prove that the recursion is well founded even with a termination_by clause.
-- so, it can't use the fact that the prior rules mean you don't need to worry about y==0
-- for the second rule...?
def add3 : Nat → Nat → Nat → Nat
  | 0, 0, z => z
  | 0, y + 1, z => 1 + (add3 0 y z)
  | x + 1, y, z => 1 + (add3 x y z)

-- Properties about trinary addition function
def prop_add3_spec   (x: Nat) (y: Nat) (z: Nat) := add3 x y z == x + (y + z)
def prop_add3_rot    (x: Nat) (y: Nat) (z: Nat) := add3 x y z == add3 y x z
def prop_add3_rrot   (x: Nat) (y: Nat) (z: Nat) := add3 x y z == add3 z x y
def prop_add3_comm12 (x: Nat) (y: Nat) (z: Nat) := add3 x y z == add3 y x z
def prop_add3_comm23 (x: Nat) (y: Nat) (z: Nat) := add3 x y z == add3 x z y
def prop_add3_comm13 (x: Nat) (y: Nat) (z: Nat) := add3 x y z == add3 z y x
def prop_add3_assoc1 (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) := add3 (add3 x1 x2 x3) x4 x5 == add3 x1 x2 (add3 x3 x4 x5)
def prop_add3_assoc2 (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) := add3 (add3 x1 x2 x3) x4 x5 == add3 x1 (add3 x2 x3 x4) x5
def prop_add3_assoc3 (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) := add3 x1 (add3 x2 x3 x4) x5 == add3 x1 x2 (add3 x3 x4 x5)

def add3acc : Nat → Nat → Nat → Nat
  | 0, 0, z => z
  | 0, y + 1, z => add3 0 y z.succ
  | x + 1, y, z => add3 x y.succ z

-- Property about accumulative trinary addition function
def prop_add3acc_spec   (x: Nat) (y: Nat) (z: Nat) := add3acc x y z == x + (y + z)
def prop_add3acc_rot    (x: Nat) (y: Nat) (z: Nat) := add3acc x y z == add3acc y x z
def prop_add3acc_rrot   (x: Nat) (y: Nat) (z: Nat) := add3acc x y z == add3acc z x y
def prop_add3acc_comm12 (x: Nat) (y: Nat) (z: Nat) := add3acc x y z == add3acc y x z
def prop_add3acc_comm23 (x: Nat) (y: Nat) (z: Nat) := add3acc x y z == add3acc x z y
def prop_add3acc_comm13 (x: Nat) (y: Nat) (z: Nat) := add3acc x y z == add3acc z y x
def prop_add3acc_assoc1 (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) := add3acc (add3acc x1 x2 x3) x4 x5 == add3acc x1 x2 (add3acc x3 x4 x5)
def prop_add3acc_assoc2 (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) := add3acc (add3acc x1 x2 x3) x4 x5 == add3acc x1 (add3acc x2 x3 x4) x5
def prop_add3acc_assoc3 (x1: Nat) (x2: Nat) (x3: Nat) (x4: Nat) (x5: Nat) := add3acc x1 (add3acc x2 x3 x4) x5 == add3acc x1 x2 (add3acc x3 x4 x5)
def prop_add3_same (x: Nat) (y: Nat) (z: Nat) := add3 x y z == add3acc x y z

-- a * b + c + d
def op : Nat → Nat → Nat → Nat → Nat
  | 0, _b, 0, d => d
  | a+1, b , 0, d => op a b b d
  | a, b, c+1, d => op a b c (d+1)

-- Property about a 4-adic operation over natural numbers
def prop_op_spec (a: Nat) (b: Nat) (c: Nat) (d: Nat) := op a b c d == a * b + c + d
def prop_op_comm_comm (a: Nat) (b: Nat) (c: Nat) (d: Nat) := op a b c d == op b a d c
def prop_op_assoc (a: Nat) (b: Nat) (c: Nat) (d: Nat) (e: Nat) := op (op a b 0 0) c d e == op a (op b c 0 0) d e
def prop_op_assoc2 (x: Nat) (a: Nat) (b: Nat) (c: Nat) (d: Nat) := op (op x a a a) b c d == op a (op b x b b) c d

-- Binary multiplication function with an interesting recursion structure,
-- which calls an accumulative trinary addition function.
def mul2 : Nat → Nat → Nat
  | 0, _y => 0
  | _x, 0 => 0
  | x + 1, y + 1 => 1 + (add3acc x y (mul2 x y))

def prop_mul2_comm (x: Nat) (y: Nat) := mul2 x y == mul2 y x
def prop_mul2_assoc (x y z : Nat) := mul2 x (mul2 y z) == mul2 (mul2 x y) z

-- (x+1)(y+1)(z+1) =  xyz + (xy + xz + yz) + (x + y + z) + 1
def mul3 : Nat → Nat → Nat → Nat
  | 0, _y, _z => 0
  | _x, 0, _z => 0
  | _x, _y, 0 => 0
  | 1, 1, 1 => 1
  | x+1, y+1, z+1 => 1 + (add3
                    (mul3 x y z)
                    (add3 (mul3 1 y z)
                          (mul3 x 1 z)
                          (mul3 x y 1))
                    (add3 x y z)
                    )
  termination_by x y z => x + y + z

-- Property about a trinary multiplication function, defined in terms of an
-- trinary addition function
-- mul3 x y z = xyz + (xy + xz + yz) + (x + y + z) + 1
def prop_mul3_spec   (x y z: Nat) := mul3 x y z == x * y * z
def prop_mul3_rot    (x y z: Nat) := mul3 x y z == mul3 y x z
def prop_mul3_rrot   (x y z: Nat) := mul3 x y z == mul3 z x y
def prop_mul3_comm12 (x y z: Nat) := mul3 x y z == mul3 y x z
def prop_mul3_comm23 (x y z: Nat) := mul3 x y z == mul3 x z y
def prop_mul3_comm13 (x y z: Nat) := mul3 x y z == mul3 z y x
def prop_mul3_assoc1 (x1 x2 x3 x4 x5: Nat) := mul3 (mul3 x1 x2 x3) x4 x5 == mul3 x1 x2 (mul3 x3 x4 x5)
def prop_mul3_assoc2 (x1 x2 x3 x4 x5: Nat) := mul3 (mul3 x1 x2 x3) x4 x5 == mul3 x1 (mul3 x2 x3 x4) x5
def prop_mul3_assoc3 (x1 x2 x3 x4 x5: Nat) := mul3 x1 (mul3 x2 x3 x4) x5 == mul3 x1 x2 (mul3 x3 x4 x5)

def mul3acc : Nat → Nat → Nat → Nat
  | 0, _y, _z => 0
  | _x, 0, _z => 0
  | _x, _y, 0 => 0
  | 1, 1, 1 => 1
  | x+1, y+1, z+1 => 1 + (add3acc
                    (mul3acc x y z)
                    (add3acc (mul3 1 y z)
                          (mul3 x 1 z)
                          (mul3 x y 1))
                    (add3acc x y z)
                    )
  termination_by x y z => x + y + z



-- Property about a trinary multiplication function, defined in terms of an
-- accumulative trinary addition function
-- mul3acc x y z = xyz + (xy + xz + yz) + (x + y + z) + 1
def prop_mul3acc_spec   (x y z: Nat) := mul3acc x y z == x * y * z
def prop_mul3acc_rot    (x y z: Nat) := mul3acc x y z == mul3acc y x z
def prop_mul3acc_rrot   (x y z: Nat) := mul3acc x y z == mul3acc z x y
def prop_mul3acc_comm12 (x y z: Nat) := mul3acc x y z == mul3acc y x z
def prop_mul3acc_comm23 (x y z: Nat) := mul3acc x y z == mul3acc x z y
def prop_mul3acc_comm13 (x y z: Nat) := mul3acc x y z == mul3acc z y x
def prop_mul3acc_assoc1 (x1 x2 x3acc x4 x5: Nat) := mul3acc (mul3acc x1 x2 x3acc) x4 x5 == mul3acc x1 x2 (mul3acc x3acc x4 x5)
def prop_mul3acc_assoc2 (x1 x2 x3acc x4 x5: Nat) := mul3acc (mul3acc x1 x2 x3acc) x4 x5 == mul3acc x1 (mul3acc x2 x3acc x4) x5
def prop_mul3acc_assoc3 (x1 x2 x3acc x4 x5: Nat) := mul3acc x1 (mul3acc x2 x3acc x4) x5 == mul3acc x1 x2 (mul3acc x3acc x4 x5)
def prop_mul3_same  (x y z: Nat) := mul3 x y z == mul3acc x y z

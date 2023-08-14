--gotten from https://github.com/leanprover/lean4-samples/blob/main/NaturalNumbers/MyNat/Definition.lean

--import statements
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

--definition of meow_nat
inductive meow_nat where
  | zero : meow_nat
  | succ : meow_nat → meow_nat
  deriving Repr, BEq, DecidableEq, Inhabited

namespace meow_nat

instance : Inhabited meow_nat where
  default := zero

--definition of simple functions
def meownat_from_nat (n : Nat) : meow_nat :=
  match n with
  | Nat.zero   => zero
  | Nat.succ a => succ (meownat_from_nat a)

def nat_from_meownat (n : meow_nat) : Nat :=
  match n with
  | zero   => Nat.zero
  | succ a => Nat.succ (nat_from_meownat a)

instance : OfNat meow_nat n where
  ofNat := meownat_from_nat n

instance : ToString meow_nat where
  toString s := toString (nat_from_meownat s)

--definition of addition
def add : meow_nat → meow_nat → meow_nat
  | a, 0      => a
  | a, succ b => succ (add a b)

instance : Add meow_nat where
  add := meow_nat.add

--test cases to check validity
#eval nat_from_meownat (meownat_from_nat (3) + meownat_from_nat (6))
#eval nat_from_meownat (meownat_from_nat (10) + meownat_from_nat (17))
#eval nat_from_meownat (meownat_from_nat (6) + meownat_from_nat (3))
#eval nat_from_meownat (meownat_from_nat (17) + meownat_from_nat (10))

--definition of pred()
def pred : meow_nat → meow_nat
  | zero   => zero
  | succ n => n

def sub : meow_nat → meow_nat → meow_nat
  | 0, _      => 0
  | a, 0      => a
  | a, succ b => pred (sub a b)

instance : Sub meow_nat where
  sub := meow_nat.sub

--test cases to check validity
#eval nat_from_meownat (meownat_from_nat (3) - meownat_from_nat (6))
#eval nat_from_meownat (meownat_from_nat (10) - meownat_from_nat (17))
#eval nat_from_meownat (meownat_from_nat (6) - meownat_from_nat (3))
#eval nat_from_meownat (meownat_from_nat (17) - meownat_from_nat (10))

end meow_nat
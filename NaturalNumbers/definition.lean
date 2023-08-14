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
def meow_nat.add : meow_nat → meow_nat → meow_nat
  | a, 0 => a
  | a, succ b => succ (meow_nat.add a b)

instance : Add meow_nat where
  add := meow_nat.add

end meow_nat
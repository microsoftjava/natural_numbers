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

lemma add_zero (n : meow_nat) : n + zero = n := by
  rfl

lemma add_succ (a b : meow_nat) : a + succ b = succ (a + b) := by
  rfl

lemma zero_add (n : meow_nat) : zero + n = n := by
  induction n with
  | zero     => rfl
  | succ n h => rw [add_succ, h]

lemma add_assoc (a b c : meow_nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero      => rw [add_zero, add_zero]
  | succ d hd => rw [add_succ, add_succ, add_succ, hd]

--test cases to check validity
#eval nat_from_meownat (meownat_from_nat (3) + meownat_from_nat (6))
#eval nat_from_meownat (meownat_from_nat (10) + meownat_from_nat (17))
#eval nat_from_meownat (meownat_from_nat (6) + meownat_from_nat (3))
#eval nat_from_meownat (meownat_from_nat (17) + meownat_from_nat (10))

--definition of pred()
def pred : meow_nat → meow_nat
  | zero   => zero
  | succ n => n

--definition of subtraction
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

--definition of multiplication
def mul : meow_nat → meow_nat → meow_nat
  | _, 0      => 0
  | a, succ b => a + (mul a b)

instance : Mul meow_nat where
  mul := meow_nat.mul

--test cases to check validity
#eval nat_from_meownat (meownat_from_nat (3) * meownat_from_nat (6))
#eval nat_from_meownat (meownat_from_nat (10) * meownat_from_nat (17))
#eval nat_from_meownat (meownat_from_nat (6) * meownat_from_nat (3))
#eval nat_from_meownat (meownat_from_nat (17) * meownat_from_nat (10))

--definition of ≤
def le (a b : meow_nat) := ∃ (c : meow_nat), b = a + c

--notation
instance : LE meow_nat := ⟨le⟩

--definition of <
def lt (a b : meow_nat) := a ≤ b ∧ ¬ (b ≤ a)

--notation
instance : LT meow_nat := ⟨lt⟩

lemma le_def_iff {a b : meow_nat} :
  a ≤ b ↔ ∃ (c : meow_nat), b = a + c := by
  rfl

lemma lt_def_iff {a b : meow_nat} : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  rfl

lemma le_trans {a b k : meow_nat} (h : a ≤ b) : b ≤ k → a ≤ k := by
  intro h₁
  cases h with
  | intro d h => 
      cases h₁ with
      | intro e h₁ =>
        exists (d + e)
        rw [h] at h₁
        rw [← add_assoc]
        exact h₁

lemma eq_means_le {a b : meow_nat} : a = b → a ≤ b := by
  intro h
  exists zero
  rw [add_zero]
  exact h.symm

lemma eq_means_le_with_h {a b : meow_nat} (h : a = b) : a ≤ b := by
  exists zero
  rw [add_zero]
  exact h.symm

lemma plus_means_le {a b c : meow_nat} : a = b + c → b ≤ a := by
  intro h
  exists c

lemma lt_of_lt_of_le {n m k : meow_nat} : n < m → m ≤ k → n < k := by
  intros h h₁
  rw [lt_def_iff] at h
  cases h with
  | intro d hd =>
    rw [lt_def_iff]
    apply And.intro
    apply le_trans d
    exact h₁
    intro he
    apply hd
    apply le_trans h₁ he

/-
--definition of division
--I know how to define it recursively but that is not fun >:(
def div : meow_nat → meow_nat → meow_nat
  | a, b =>
    if a = b then
      1
    else
      have meow := a - b
      if b ≠ 0 ∧ meow ≠ 0 then
      --if h : 0 < b ∧ b ≤ a then
        1 + div meow b
      else
        0

instance : Div meow_nat where
  div := meow_nat.div

--test cases to check validity

#eval nat_from_meownat (meownat_from_nat (3) / meownat_from_nat (6))
#eval nat_from_meownat (meownat_from_nat (10) / meownat_from_nat (17))
#eval nat_from_meownat (meownat_from_nat (6) / meownat_from_nat (3))
#eval nat_from_meownat (meownat_from_nat (17) / meownat_from_nat (10))
-/
end meow_nat
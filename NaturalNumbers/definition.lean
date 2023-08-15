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

/-=====================================================
                  addition theorems
  =====================================================-/

theorem nat_0_is_0 : 0 = zero := by
  rfl

theorem one_is_succ_0 : 1 = succ zero := by
  rfl

theorem add_0 (a : meow_nat) : a + zero = a := by
  rfl

theorem add_nat_0 (a : meow_nat) : a + 0 = a := by
  rfl

theorem add_succ_0 (a : meow_nat) : a + succ zero = succ a := by
  rfl

theorem add_succ_nat_0 (a : meow_nat) : a + succ 0 = succ a := by
  rfl

theorem add_one (a : meow_nat) : a + 1 = succ a := by
  rfl

theorem add_succ (a b : meow_nat) : a + succ b = succ (a + b) := by
  rfl

theorem _0_add (a : meow_nat) : zero + a = a := by
  induction a with
  | zero     => rfl
  | succ a h => rw [add_succ, h]

theorem nat_0_add (a : meow_nat) : 0 + a = a := by
  induction a with
  | zero     => rfl
  | succ a h => rw [add_succ, h]

theorem succ_0_add (a : meow_nat) : succ zero + a = succ a := by
  induction a with
  | zero     => rw [add_0]
  | succ a h => rw [add_succ, h]

theorem succ_nat_0_add (a : meow_nat) : succ 0 + a = succ a := by
  induction a with
  | zero     => rw [add_0, nat_0_is_0]
  | succ a h => rw [add_succ, h]

theorem one_add (a : meow_nat) : 1 + a = succ a := by
  induction a with
  | zero     => rw [add_0, one_is_succ_0]
  | succ a h => rw [add_succ, h]

theorem succ_add (a b : meow_nat) : succ a + b = succ (a + b) := by
  induction b with
  | zero     => rw [add_0, add_0]
  | succ b h => rw [add_succ, h, add_succ]

theorem add_assoc (a b c : meow_nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero      => rw [add_0, add_0]
  | succ c hc => rw [add_succ, add_succ, add_succ, hc]

theorem add_comm (a b : meow_nat) : a + b = b + a := by
  induction b with
  | zero     => rw [add_0, _0_add]
  | succ b h => rw [add_succ, succ_add, h]

theorem add_left_comm (a b c : meow_nat) : a + b + c = b + a + c := by
  rw [add_comm a b]

theorem add_right_comm (a b c : meow_nat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

theorem add_sides_comm (a b c : meow_nat) : a + b + c = c + b + a := by
  rw [add_comm, add_comm a b, ← add_assoc]

theorem eq_means_succ_eq {a b : meow_nat} : a = b → succ a = succ b := by
  intro h
  rw [h]

axiom succ_eq_means_eq {a b : meow_nat} : succ a = succ b → a = b

axiom _0_ne_succ (a : meow_nat) : zero ≠ succ a

axiom nat_0_ne_succ (a : meow_nat) : 0 ≠ succ a

theorem succ_ne_0 (a : meow_nat) : succ a ≠ zero := by
  exact (_0_ne_succ a).symm

theorem succ_ne_nat_0 (a : meow_nat) : succ a ≠ 0 := by
  exact (nat_0_ne_succ a).symm

theorem eq_iff_succ_eq (a b : meow_nat) : a = b ↔ succ a = succ b := by
  apply Iff.intro
  exact eq_means_succ_eq
  exact succ_eq_means_eq

theorem add_left_cancel (a b t : meow_nat) : t + a = t + b → a = b := by
  intro h
  induction t with
  | zero      => rwa [_0_add, _0_add] at h
  | succ t ht => rw [succ_add, succ_add] at h
                 rw [ht]
                 exact succ_eq_means_eq h

theorem add_right_cancel (a b t : meow_nat) : a + t = b + t → a = b := by
  intro h
  induction t with
  | zero      => rwa [add_0, add_0] at h
  | succ t ht => rw [add_succ, add_succ] at h
                 rw [ht]
                 exact succ_eq_means_eq h

theorem add_left_cancel_iff (a b t : meow_nat) : t + a = t + b ↔ a = b := by
  apply Iff.intro
  exact add_left_cancel _ _ _
  intro meow
  rw [meow]

theorem add_right_cancel_iff (a b t : meow_nat) : a + t = b + t ↔ a = b := by
  apply Iff.intro
  exact add_right_cancel _ _ _
  intro meow
  rw [meow]

theorem AplusBeqAsoBeq0 {a b : meow_nat} : a + b = a → b = zero := by
  rw [← add_0 a, add_assoc, _0_add]
  exact add_left_cancel _ _ _

theorem AplusBeqAsoBeqNat0 {a b : meow_nat} : a + b = a → b = 0 := by
  rw [← add_0 a, add_assoc, _0_add]
  exact add_left_cancel _ _ _

theorem AplusBeqBsoAeq0 {a b : meow_nat} : a + b = b → a = zero := by
  rw [← _0_add b, ← add_assoc, add_0]
  exact add_right_cancel _ _ _

theorem AplusBeqBsoAeqNat0 {a b : meow_nat} : a + b = b → a = 0 := by
  rw [← _0_add b, ← add_assoc, add_0]
  exact add_right_cancel _ _ _

theorem sum0soAeq0 {a b : meow_nat} (h : a + b = zero) : a = zero := by
  cases a with
  | zero   => rfl
  | succ a => rw [succ_add] at h; exfalso; exact succ_ne_0 (a + b) h

/-=====================================================
              end of addition theorems
  =====================================================-/

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

/-=====================================================
                  inequality theorems
  =====================================================-/

theorem le_def_iff {a b : meow_nat} :
  a ≤ b ↔ ∃ (c : meow_nat), b = a + c := by
  rfl

theorem lt_def_iff {a b : meow_nat} : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  rfl

theorem le_trans {a b k : meow_nat} (h : a ≤ b) : b ≤ k → a ≤ k := by
  intro h₁
  cases h with
  | intro d h => 
      cases h₁ with
      | intro e h₁ =>
        exists (d + e)
        rw [h] at h₁
        rw [← add_assoc]
        exact h₁

theorem eq_means_le {a b : meow_nat} : a = b → a ≤ b := by
  intro h
  exists zero
  rw [add_0]
  exact h.symm

theorem eq_means_le_with_h {a b : meow_nat} (h : a = b) : a ≤ b := by
  exists zero
  rw [add_0]
  exact h.symm

theorem plus_means_le {a b c : meow_nat} : a = b + c → b ≤ a := by
  intro h
  exists c

theorem lt_of_lt_of_le {n m k : meow_nat} : n < m → m ≤ k → n < k := by
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

/-=====================================================
              end of inequality theorems
  =====================================================-/

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
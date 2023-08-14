--gotten from https://github.com/PatrickMassot/NNG4/blob/main/NNG/MyNat.lean

axiom meow_nat : Type

axiom succ : meow_nat → meow_nat

@[instance] axiom meow_of_nat (n : Nat) : OfNat meow_nat n

@[instance] axiom meow_add : HAdd meow_nat meow_nat meow_nat

@[instance] axiom meow_sub : HSub meow_nat meow_nat meow_nat

@[instance] axiom meow_mul : HMul meow_nat meow_nat meow_nat

@[instance] axiom meow_div : HDiv meow_nat meow_nat meow_nat

@[instance] axiom meow_pow : HPow meow_nat meow_nat meow_nat

@[elabAsElim] axiom meow_induction {P : meow_nat → Prop}
(n : meow_nat) (h₀ : P 0) (h : ∀ n, P n → P (succ n)) : P n

axiom add_zero : ∀ a : meow_nat, a + 0 = a

axiom add_succ : ∀ a b : meow_nat, a + succ b = succ (a + b)
--gotten from https://github.com/PatrickMassot/NNG4/blob/main/NNG/MyNat.lean
axiom meow_nat : Type

axiom succ :
meow_nat → meow_nat

@[instance]
axiom meow_of_nat (n : Nat) :
OfNat meow_nat n

@[instance]
axiom meow_add :
HAdd meow_nat meow_nat meow_nat

@[instance]
axiom meow_sub :
HSub meow_nat meow_nat meow_nat

@[instance]
axiom meow_mul :
HMul meow_nat meow_nat meow_nat

@[instance]
axiom meow_div :
HDiv meow_nat meow_nat meow_nat

@[instance]
axiom meow_pow :
HPow meow_nat meow_nat meow_nat
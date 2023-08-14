import NaturalNumbers.definition

namespace meow_nat

--definition of ≤
def le (a b : meow_nat) := ∃ (c : meow_nat), b = a + c

--notation
instance : LE meow_nat := ⟨le⟩

--definition of <
def lt (a b : meow_nat) := a ≤ b ∧ ¬ (b ≤ a)

--notation
instance : LT meow_nat := ⟨lt⟩

end meow_nat
import NaturalNumbers.definition

namespace meow_nat

def le (a b : meow_nat) := ∃ (c : meow_nat), b = a + c

--notation
instance : LE meow_nat := ⟨le⟩

end meow_nat
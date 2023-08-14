import NaturalNumbers.definition
namespace meow_nat

def le (a b : meow_nat) := ∃ (c : meow_nat), b = a + c

end meow_nat
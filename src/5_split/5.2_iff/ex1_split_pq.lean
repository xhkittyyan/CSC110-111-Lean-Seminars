import tactic

open_locale classical

-- BEGIN

example (P Q : Prop) (h₁ : P → Q) (h₂ : Q → P) : P ↔ Q :=
begin 
  split, 
  { exact h₁, },
  { exact h₂, },
end

-- END
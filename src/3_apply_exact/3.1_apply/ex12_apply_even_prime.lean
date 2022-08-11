import data.nat.prime data.nat.parity

open nat

-- BEGIN
variable (s : set ℕ)

example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, nat.prime x) :
  ∀ x ∈ s, ¬ even x ∧ nat.prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs,
end

-- END
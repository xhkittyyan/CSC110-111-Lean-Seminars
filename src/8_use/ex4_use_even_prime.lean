import data.nat.prime data.nat.parity

open nat

-- BEGIN
variable (s : set ℕ)

example (h : ∃ x ∈ s, ¬ even x ∧ nat.prime x) :
  ∃ x ∈ s, nat.prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x],
end
-- END
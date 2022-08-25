import data.nat.prime

open nat

-- BEGIN
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin
  cases h with h1 h2,
  sorry,
end
-- END
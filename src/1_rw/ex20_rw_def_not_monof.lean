import data.real.basic

-- BEGIN
theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

example : ¬ monotone (λ x : ℝ, -x) :=
begin
  rw monotone, 
  push_neg,
  use -2,
  use -1,
  norm_num,
end
-- END
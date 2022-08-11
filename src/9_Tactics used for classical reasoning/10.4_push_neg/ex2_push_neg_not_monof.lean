import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

open_locale classical

variable (f : ℝ → ℝ)

-- BEGIN
example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  simp only [monotone] at h,
  push_neg at h,
  exact h,
end

/- The rw tactic also unpacks a definition, which is equivalent to 
'simp only' -/
example : ¬ monotone (λ x : ℝ, -x) :=
begin
  rw monotone, 
  push_neg,
  use -2,
  use -1,
  norm_num,
end
-- END
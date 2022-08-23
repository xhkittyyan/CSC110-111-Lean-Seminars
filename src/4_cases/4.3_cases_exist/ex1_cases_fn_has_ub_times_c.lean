import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variables {f g : ℝ → ℝ}

-- BEGIN

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a ubfa,
  use c * a,
  intro x,
  dsimp,
  exact mul_le_mul_of_nonneg_left (ubfa x) h,
end
-- END
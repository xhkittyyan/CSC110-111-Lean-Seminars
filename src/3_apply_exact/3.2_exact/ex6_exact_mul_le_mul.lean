import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variables (f g : ℝ → ℝ)

-- BEGIN
example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
begin
  intros a b aleb,
  dsimp,
  have : f a ≤ f b,
    from mf aleb,
  exact mul_le_mul_of_nonneg_left this nnc,
end

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
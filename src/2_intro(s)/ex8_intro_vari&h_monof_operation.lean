import data.real.basic

variables (f g : ℝ → ℝ)

#check mul_le_mul_of_nonneg_left

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

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb,
end

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
begin 
  intros a b aleb,
  dsimp,
  apply mf,
  apply mg,
  apply aleb,
end
-- END
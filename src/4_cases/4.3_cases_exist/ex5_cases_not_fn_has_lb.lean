import data.real.basic


def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

-- BEGIN
example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  intro fnlb,
  cases fnlb with a fnlba,
  cases h a with x hx,
  have : f x ≥ a,
    from fnlba x,
  linarith,
end
-- END
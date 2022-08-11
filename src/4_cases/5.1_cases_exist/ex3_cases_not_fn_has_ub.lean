import data.real.basic

variable f : ℝ → ℝ

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

-- BEGIN
example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith,
end

example : ¬ fn_has_ub (λ x, x) :=
begin
  intro fnub,
  cases fnub with a fnuba,
  have a_plus_1_le_a := fnuba (a + 1),
  simp at a_plus_1_le_a,
  linarith,
end

-- END
import data.real.basic

-- BEGIN
example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  { intros a b hab,
  exact rfl.ge, },
  have h1 : f 1 ≤ f 0,
    from le_refl _,
  have h2 : (1 : ℝ) ≤ 0 := h monof h1,
  exact not_lt_of_le h2 zero_lt_one,
end

-- END
import data.real.basic

-- BEGIN
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁,
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  intro h,
  cases h with h₀ h₁, 
  intro h',
  exact h₁ (le_antisymm h₀ h'),
end

/- using rcases instead of intros and cases -/
example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h'),
end

/- using λ abstraction -/
example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')

/- you will see that by_contra h' is equivalent to intro h' -/
example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  intro h,
  cases h with h₀ h₁, 
  by_contra h',
  exact h₁ (le_antisymm h₀ h'),
end


-- END
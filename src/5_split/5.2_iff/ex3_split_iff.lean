import data.real.basic

-- BEGIN
example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
    intro h1,
    intro h2,
    rw h2 at h1,
    rw h2 at h,
    exact h1 h,
  intro h1,
  contrapose! h1,
  exact le_antisymm h h1,
end

-- Alternatively
example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
    intro h1,
    push_neg at h1,
    intro h2,
    rw h2 at h1,
    exact (lt_irrefl y) h1,
  intro h1,
  contrapose! h1,
  exact le_antisymm h h1,
end

-- Alternatively
example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
  { contrapose!,
    rintro rfl,
    reflexivity },
  contrapose!,
  exact le_antisymm h,
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩
-- END
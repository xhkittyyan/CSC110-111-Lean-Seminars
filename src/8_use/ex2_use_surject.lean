import data.real.basic

open function

-- BEGIN
example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, ring
end

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x, 
  dsimp,
  use x / c,
  sorry,
end

/- Alternatively, using the field_simp tactic -/

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x, 
  dsimp,
  use x / c,
  field_simp, /- clear denominators in a useful way -/
  sorry,
end
-- END
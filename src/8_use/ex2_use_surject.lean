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
  rw ← mul_one_div,
  rw mul_comm,
  rw mul_assoc,
  rw div_mul_cancel,
  rw mul_one,
  exact h,
end

/- Alternatively, using the field_simp tactic -/

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x, 
  dsimp,
  use x / c,
  field_simp, /-clear denominators in a useful way-/
  rw mul_comm,
end
-- END
import data.real.basic

-- BEGIN
theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0 := ((add_eq_zero_iff' (sq_nonneg x) (sq_nonneg y)).mp h).1,
  exact pow_eq_zero h',
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin 
  split;
  intro h,
  { split,
    exact aux h,
    exact aux (by linarith : y^2 + x^2 = 0), },
  { cases h with hr1 hr2,
    rw hr1,
    rw hr2,
    norm_num, }
end
-- END
import data.real.basic

variables {x y : ℝ}

namespace my_abs

-- BEGIN
theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  split; intro h,
  { cases lt_or_ge y 0 with y_neg y_nonneg,
    { rw abs_of_neg y_neg at h, right, exact h, },
    { rw abs_of_nonneg y_nonneg at h, left, exact h, }, },
  { cases h with x_lt_y x_lt_neg_y,
    linarith [le_abs_self y],
    linarith [neg_le_abs_self y], }
end

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  split; intro h,
  { split,
    linarith [neg_abs_le_self x],
    linarith [le_abs_self x], },
  { cases lt_or_ge x 0 with x_neg x_nonneg,
    { rw abs_of_neg x_neg, linarith only [h.1], },
    { rw abs_of_nonneg x_nonneg, exact h.2 }, },
end
-- END

end my_abs
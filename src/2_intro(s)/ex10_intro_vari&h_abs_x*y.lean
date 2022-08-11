import data.real.basic

#check mul_lt_mul_right
#check @lt_of_lt_of_le

-- BEGIN
lemma my_lemma : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
    abs (x * y) = abs x * abs y : by rw abs_mul
    ... ≤ abs x * ε             : mul_le_mul_of_nonneg_left (le_of_lt ylt) (abs_nonneg x)
    ... < 1 * ε                 : mul_lt_mul_of_pos_right (lt_of_le_of_lt' ele1 xlt) epos
    ... = ε                     : by rw one_mul,
end
-- END
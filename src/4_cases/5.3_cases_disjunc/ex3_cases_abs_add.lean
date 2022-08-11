import data.real.basic

variables {x y : ℝ}

#check lt_or_le
#check @abs_of_neg
#check @abs_of_nonneg

namespace my_abs

-- BEGIN

theorem abs_add : abs (x + y) ≤ abs x + abs y :=
begin
  cases lt_or_le x 0 with hx hx;
  cases lt_or_le y 0 with hy hy;
  cases lt_or_le (x + y) 0 with hxy hxy;
  simp [abs_of_neg, abs_of_nonneg, hx, hy, hxy];
  linarith,
end

-- END

end my_abs
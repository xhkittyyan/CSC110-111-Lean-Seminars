import data.real.basic

variables {x y : ℝ}

#check le_or_lt
#check @abs_of_neg
#check @abs_of_nonneg

-- BEGIN
example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h1 h2, 
  { rw abs_of_nonneg h1,
    sorry, },
  rw abs_of_neg h2,
  sorry,
end
-- END
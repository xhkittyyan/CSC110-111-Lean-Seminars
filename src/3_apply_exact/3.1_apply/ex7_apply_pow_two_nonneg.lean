import data.real.basic tactic

variables a b : ℝ

#check pow_two_nonneg
#check pow_two_nonneg b
#check ring

-- BEGIN
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0                       : by apply pow_two_nonneg,
  linarith,
end
-- END
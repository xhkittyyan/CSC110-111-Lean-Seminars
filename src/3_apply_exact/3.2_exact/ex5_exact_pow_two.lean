import data.real.basic tactic

variables a b : ℝ

#check le_refl
#check le_refl (a * b) 
#check add_le_add
#check pow_two_nonneg
#check ring

-- BEGIN
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2     : by ring
    ... ≥ 0                           : by exact pow_two_nonneg (a-b),
  calc
    2*a*b
        = 2*a*b + 0                   : by ring
    ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : by exact add_le_add (le_refl (2 * a * b)) h
    ... = a^2 + b^2                   : by ring
end
-- END
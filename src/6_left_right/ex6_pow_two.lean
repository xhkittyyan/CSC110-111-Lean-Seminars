import data.real.basic

#check pow_two 

variables (x y : ℝ)

-- BEGIN
example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  have h' : (x + 1) * (x - 1) = 0,
  calc (x + 1) * (x - 1) = x^2 - 1 : by ring
  ...                    = 1 - 1 : by rw h
  ...                    = 0 : by norm_num,
  have h'' : x + 1 = 0 ∨ x - 1 = 0 := mul_eq_zero.mp h',
    cases h'',
    right,
    exact add_eq_zero_iff_eq_neg.mp h'',
    left,
    exact sub_eq_zero.mp h'',
end

example (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  have h' : (x + y) * (x - y) = 0,
  calc (x + y) * (x - y) = x^2 - y^2 : by ring
  ...                    = y^2 - y^2 : by rw h
  ...                    = 0 : sub_self (y ^ 2),
  have h'' : x + y = 0 ∨ x - y = 0 := mul_eq_zero.mp h',
    cases h'',
    right,
    exact add_eq_zero_iff_eq_neg.mp h'',
    left,
    exact sub_eq_zero.mp h'',
end

-- END
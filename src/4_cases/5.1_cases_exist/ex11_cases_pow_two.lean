import data.real.basic

variables a b c : ℝ

#check pow_two_nonneg
#check pow_two_nonneg b
#check @add_le_add

-- BEGIN
example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
begin
  cases h with a ha,
  cases ha with b hb,
  have ha2 : a ^ 2 ≥ 0,
    from pow_two_nonneg a,
  have hb2 : b ^ 2 ≥ 0,
    from pow_two_nonneg b,
  have ha2b2 := add_nonneg ha2 hb2,
  cases hb,
  { rw hb, exact ha2b2 },
  { rw hb, exact add_nonneg ha2b2 zero_le_one },
end
-- END
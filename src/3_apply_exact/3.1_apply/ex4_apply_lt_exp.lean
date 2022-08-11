import analysis.special_functions.exp

open real

variables a b c d e : ℝ

#check le_refl
#check add_lt_add_of_lt_of_le
#check add_lt_add_of_le_of_lt
#check exp_lt_exp.mpr

-- BEGIN
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt h₀,
    apply exp_lt_exp.mpr h₁ },
  apply le_refl,
end
-- END
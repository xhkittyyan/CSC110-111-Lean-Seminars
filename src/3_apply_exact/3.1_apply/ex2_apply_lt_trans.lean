import data.real.basic

variables a b c : ℝ

#check lt_trans
#check lt_of_le_of_lt

-- BEGIN
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) : a < e :=
begin
  apply lt_of_le_of_lt h₀,
  apply lt_trans h₁,
  apply lt_of_le_of_lt h₂,
  exact h₃,
end 

-- END
import analysis.special_functions.exp
import data.real.basic
import tactic

open real

variables a b : ℝ

#check pow_two_nonneg
#check pow_two_nonneg b
#check @exp_le_exp 
#check exp_le_exp.mpr

-- BEGIN
example (a : ℝ) : 0 ≤ a^2 :=
begin
  exact pow_two_nonneg a,
end

example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h,
end
-- END
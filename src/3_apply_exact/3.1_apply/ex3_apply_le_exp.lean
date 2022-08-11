import analysis.special_functions.exp
import tactic

open real

variables a b c : ℝ

#check le_refl
#check sub_le_sub
#check exp_le_exp
#check exp_le_exp.mpr

-- BEGIN

example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  apply sub_le_sub,
    apply le_refl,
  apply exp_le_exp.mpr h,
end

-- END
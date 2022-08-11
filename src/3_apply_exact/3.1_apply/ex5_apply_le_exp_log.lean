import analysis.special_functions.exp
import analysis.special_functions.log.basic

/- Tactics you may consider
-apply
-exact
-have
-norm_num: deals with numerical expressions 
-/

open real
variables a b c d e : ℝ

#check le_refl
#check le_refl b
#check add_pos
#check add_le_add
#check add_le_add_left
#check exp_pos
#check exp_pos d
#check exp_le_exp.mpr
#check log_le_log

-- BEGIN
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add,
    apply le_refl c,
    apply exp_le_exp.mpr,
  apply add_le_add,
   apply le_refl a,
   apply h₀,
end

example : (0 : ℝ) < 1 :=
by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { apply add_pos, 
    norm_num, 
    exact exp_pos a},
  have h₁ : 0 < 1 + exp b,
  { apply add_pos, 
    norm_num, 
    exact exp_pos b},
  apply (log_le_log h₀ h₁).mpr,
   { apply add_le_add_left, 
    apply exp_le_exp.mpr h, },
end
-- END
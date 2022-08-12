import data.real.basic
import algebra.ring
import algebra.group
import analysis.special_functions.exp
import analysis.special_functions.log.base

-- BEGIN
section
variables a b c : ℝ
variables (R : Type*) [ring R]

#check (add_comm : ∀ a b : R, a + b = b + a)
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_zero : ∀ a : R, a + 0 = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_comm b a : b * a = a * b)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
end

section
variables (G : Type*) [group G]

#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
#check (mul_right_inv : ∀ a : G, a * a⁻¹ = 1)
end

/- Inequalities -/
variables a b c d: ℝ
variables (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
#check (lt_irrefl a : ¬ a < a)
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

/- Negation-/
#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)

/- You can be explicit about the variables when needed. 
Check out the differences between the #checks below -/
section
#check mul_comm
#check @mul_comm
#check mul_comm a
#check mul_comm a b
#check mul_comm b a 
end
--END
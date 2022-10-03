import data.real.basic
import data.real.irrational
import data.real.sqrt
import analysis.special_functions.pow

def rational (x : ℝ) := ∃ a b : ℤ, x = a / b

notation `√` a := real.sqrt a

/- Prove that there exist irrational numbers a and b such that a ^ b is rational.
   A paper-pencil proof:
   Let a = b = √2.
   Since a ^ b is either rational or not rational, we have two cases:
   Case 1, if a ^ b is rational, then the result is proved.  
   Case 2, if a ^ b is irrational, take b' = √2.
      (a ^ b) ^ b' = (√2 ^ √2) ^ √2 = √2 ^ (√2 * √2) = 2, which is rational.
  In any case, we proved that there exist irrational numbers a and b such that a ^ b is rational. 
  Q.E.D.
-/

lemma rational_two : rational 2 :=
begin
  use [2, 1],
  norm_num,
end

lemma irrational_of_not_rational {x : ℝ} (h : ¬ rational x) : irrational x :=
begin
  rw irrational_iff_ne_rational,
  rw rational at h,
  push_neg at h,
  exact h,
end

example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ rational (a ^ b) :=
begin
  let a := √2,
  let b := √2,
  by_cases rational (a ^ b),
  { use [a, b],
    exact ⟨irrational_sqrt_two, irrational_sqrt_two, h⟩, },
  { let b' := √2,
    use [a ^ b, b'],
    have rational_exp : rational ((a ^ b) ^ b'),
    { have exp_eq_2 : (a ^ b) ^ b' = 2,
      calc (a ^ b) ^ b' = ((√2) ^ √2) ^ √2 : by refl
      ...               = (√2) ^ ((√2) * √2) : by rw ← real.rpow_mul (real.sqrt_nonneg 2)
      ...               = 2 : by simp,
      rw exp_eq_2,
      exact rational_two, },
      exact ⟨irrational_of_not_rational h, irrational_sqrt_two, rational_exp⟩,
    },
end

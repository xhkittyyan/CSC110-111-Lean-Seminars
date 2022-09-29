import data.real.basic
import data.real.irrational
import data.real.sqrt
import analysis.special_functions.pow

def rational (x : ℝ) := ∃ a b : ℤ, x = ↑a / ↑b

-- Prove that there exists a and b that are irrationals such that a ^ b is rational.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ rational (a ^ b) :=
/- A paper-pencil proof:
   Let a = b = √2.
   Since a ^ b is either rational or not rational, we have two cases:
   Case 1, if a ^ b is rational, then the result is proved.  
   Case 2, if a ^ b is irrational, take c = √2.
      (a ^ b) ^ c = (√2 ^ √2) ^ √2 = √2 ^ (√2 * √2) = 2, which is rational.
  In any case, we proved that there exists a and b that are irrationals such that 
  a ^ b is rational. 
   Q.E.D.
-/
begin
  let c := real.sqrt 2 ^ real.sqrt 2,
  by_cases rational c,
  { use [real.sqrt 2, real.sqrt 2],
    exact ⟨irrational_sqrt_two, irrational_sqrt_two, h⟩, },
  { use [c, real.sqrt 2],
    let d := c ^ real.sqrt 2,
    have irrational_c : irrational c,
    { rw irrational_iff_ne_rational,
      rw rational at h,
      push_neg at h,
      exact h, },
    have rational_d : rational d,
    { have d_eq_2 : d = 2,
      calc d = (real.sqrt 2 ^ real.sqrt 2) ^ real.sqrt 2 : by refl
      ...    = real.sqrt 2 ^ (real.sqrt 2 * real.sqrt 2) : by rw ← real.rpow_mul (real.sqrt_nonneg 2)
      ...    = 2 : by simp,
      use [2, 1],
      rw d_eq_2,
      norm_num, },
    exact ⟨irrational_c, irrational_sqrt_two, rational_d⟩,
  }
end

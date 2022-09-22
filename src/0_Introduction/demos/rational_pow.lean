import data.real.basic
import data.real.irrational
import data.real.sqrt
import analysis.special_functions.pow

def rational (x : ℝ) := ∃ a b : ℤ, x = ↑a / ↑b

-- Prove that there exists a and b that are irrationals such that a ^ b is rational.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ rational (a ^ b) :=
/- A paper-pencil proof:
   Let c = √2 ^ √2. 
   Since c is either rational or not rational, we have two cases:
   Case 1, take a = b = √2. Then a and b are irrational and, by hypothesis, 
    a ^ b = c is rational.
   Case 2, take a = c and b = √2 and let d = a ^ b.
      a = c is irrational, since c is not rational.
      b = √2 is irrational.
      d = (√2 ^ √2) ^ √2 = √2 ^ (√2 * √2) = 2 is rational.
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

import data.real.basic
import data.real.irrational
import data.real.sqrt
import analysis.special_functions.pow

def rational (x : ℝ) := ∃ a b : ℤ, x = a / b

notation `√` a := real.sqrt a

-- Prove that there exists a and b that are irrationals such that a ^ b is rational.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ rational (a ^ b) :=
begin
let a := √2,
  let b := √2,
  let c := a ^ b,
  by_cases rational c,
 sorry,
end




example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ rational (a ^ b) :=
/- A paper-pencil proof:
   Let a = b = √2.
   Since a ^ b is either rational or not rational, we have two cases:
   Case 1, if a ^ b is rational, then the result is proved.  
   Case 2, if a ^ b is irrational, take b' = √2.
      (a ^ b) ^ b' = (√2 ^ √2) ^ √2 = √2 ^ (√2 * √2) = 2, which is rational.
  In any case, we proved that there exists a and b that are irrationals such that 
  a ^ b is rational. 
  Q.E.D.
-/
begin
  let a := √2,
  let b := √2,
  let c := a ^ b,
  by_cases rational c,
  { use [a, b],
    exact ⟨irrational_sqrt_two, irrational_sqrt_two, h⟩, },
  { let b' := √2,
    use [c, b'],
    let c' := c ^ b',
    have irrational_c : irrational c,
    { rw irrational_iff_ne_rational,
      rw rational at h,
      push_neg at h,
      exact h, },
    have rational_d : rational c',
    { have c'_eq_2 : c' = 2,
      calc c' = ((√2) ^ √2) ^ √2 : by refl
      ...    = (√2) ^ ((√2) * √2) : by rw ← real.rpow_mul (real.sqrt_nonneg 2)
      ...    = 2 : by simp,
      use [2, 1],
      rw c'_eq_2,
      norm_num, },
    exact ⟨irrational_c, irrational_sqrt_two, rational_d⟩,
  },
end

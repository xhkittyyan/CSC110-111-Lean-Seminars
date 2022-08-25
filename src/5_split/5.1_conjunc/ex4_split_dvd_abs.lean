import data.real.basic
import data.nat.gcd

open nat

-- BEGIN

/- In the follwoing example,we use dvd_gcd_iff to replace an expression of 
the form m ∣ gcd n k by the equivalent expression m ∣ n ∧ m ∣ k -/
example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split,
  norm_num,
  norm_num,
end

/- It is often convenient to rewrite a statement to an equivalent one
 In the following example, we use abs_lt to replace an expression of 
 the form abs x < y by the equivalent expression - y < x ∧ x < y -/
example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split, 
  linarith,
  linarith,
end

-- END
import data.real.basic
import data.nat.gcd

open nat

#check add_lt_add_of_lt_of_le
#check add_lt_add_of_le_of_lt
#check int.sub_lt_sub_of_lt_of_le

-- BEGIN

/- In the follwoing example,we use dvd_gcd_iff to replace an expression of 
the form m ∣ gcd n k by the equivalent expression m ∣ n ∧ m ∣ k -/
example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split,
  { use 2, norm_num,},
  { use 5, norm_num,}
end

example (x y z : ℝ) (h : x + y > z) : x > z - y :=
sub_lt_iff_lt_add.mpr h

example (x y z : ℝ) (h : x + y < z) : x < z - y :=
lt_sub_iff_add_lt.mpr h

/- It is often convenient to rewrite a statement to an equivalent one
 In the following example, we use abs_lt to replace an expression of 
 the form abs x < y by the equivalent expression - y < x ∧ x < y -/
example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  cases h with h1 h2,
  split,
  rw ← sub_lt_iff_lt_add at h1,
  norm_num at h1,
  exact h1,
  rw ← lt_sub_iff_add_lt at h2,
  norm_num at h2,
  exact h2,
end


example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  cases h with h1 h2,
  split;
  linarith,
end


-- END
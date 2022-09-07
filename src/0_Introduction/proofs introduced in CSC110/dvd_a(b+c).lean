import tactic

#check mul_add
#check dvd_mul_right
#check add_sub_cancel
#check add_sub_cancel'

variables {x d f g : ℤ}
variables {a b c : ℕ}

-- BEGIN
/- Prove that for all d ∈ ℤ, and for all x ∈ ℤ, if x divides x + d, 
   then x also divides d. -/
example (divxd : x ∣ x + d) : x ∣ d :=
begin
  cases divxd with f beq,
  have h : x ∣ x,
  use 1,
  rw mul_one,
  cases h with g xeq,
  use (f - g),
  rw mul_sub,
  rw  [←beq, ← xeq],
  rw add_sub_cancel' x d,
end

/- A similar proof: prove that for all a, b, c ∈ ℕ, if a ∣ b and a ∣ c, 
   then a ∣ (b + c). -/
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin 
  cases divab with d beq,
  cases divac with e ceq,
  rw [beq, ceq],
  rw ← mul_add,
  exact dvd_mul_right a (d + e),
end

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin 
  cases divab with d beq,
  cases divac with e ceq,
  rw [beq, ceq],
  rw ← mul_add,
  use (d + e),
end
-- END

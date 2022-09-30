import tactic

#check mul_add
#check dvd_mul_right
#check add_sub_cancel
#check add_sub_cancel'

variables {x d f g : ℤ}
variables {a b c e m n t : ℕ}

-- BEGIN
/- Prove that for x, d ∈ ℤ, if x divides x + d, 
   then x also divides d. -/
example (divxd : x ∣ x + d) : x ∣ d :=
begin
  cases divxd with f beq,
  use f - 1,
  rw mul_sub,
  rw ← beq,
  rw [mul_one, add_sub_cancel' x d], -- or, ring
end

/- A similar proof: prove that for a, b, c ∈ ℕ, if a ∣ b and a ∣ c, 
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

example (h : t ∣ m) (h' : t ∣ n) : t ∣ a * m + b * n := 
begin 
  cases h with c hc,
  cases h' with e he,
  rw [hc, he],
  rw [mul_comm, mul_assoc, mul_comm b, mul_assoc t],
  rw ← mul_add,
  use (c * a + e * b),
end
-- END

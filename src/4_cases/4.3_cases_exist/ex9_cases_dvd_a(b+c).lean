import tactic

#check mul_add
#check dvd_mul_right

variables {a b c : ℕ}

-- BEGIN
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

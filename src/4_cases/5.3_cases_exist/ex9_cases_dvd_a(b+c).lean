import tactic

variables {a b c : ℕ}

-- BEGIN
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin 
  cases divab with d beq,
  cases divac with e ceq,
  rw [ceq, beq],
  rw ← mul_add,
  use (d + e),
end
-- END

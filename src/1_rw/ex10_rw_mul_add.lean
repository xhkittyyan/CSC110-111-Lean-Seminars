import data.real.basic

variables a b c d : ℝ

#check add_assoc
#check add_mul
#check mul_add

-- BEGIN

/- a tactic proof using rw -/
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin
  rw [add_mul, mul_add, mul_add],
  rw ← add_assoc,
end 

/- a calc proof-/
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * c + a * d + (b * c + b * d) :
      by rw [add_mul, mul_add, mul_add]
  ... = a * c + a * d + b * c + b * d :
      by rw ← add_assoc
-- END


 
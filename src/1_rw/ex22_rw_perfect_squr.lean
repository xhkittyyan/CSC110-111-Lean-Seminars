import data.real.basic

variables a b c d e: ℝ

#check mul_comm
#check mul_assoc
#check add_comm
#check add_assoc (d * e)
#check add_mul
#check mul_add
#check two_mul

-- BEGIN
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul],
end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
          by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b :
          by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     :
          by rw [mul_comm b a, ←two_mul]


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      rw add_mul,
      rw [mul_add, mul_add],
      rw mul_comm b a,
    end
  ... = a * a + (b * a + a * b) + b * b : by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     : by rw [mul_comm a b, ←two_mul]
-- END
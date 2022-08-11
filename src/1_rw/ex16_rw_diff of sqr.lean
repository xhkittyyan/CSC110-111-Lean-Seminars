import data.real.basic

variables a b c d : ℝ 

#check add_mul
#check add_mul c a b
#check add_sub
#check add_sub c b a
#check sub_zero
#check sub_self
#check sub_add
#check sub_sub
#check mul_comm d c 
#check mul_sub a b c
#check pow_two d


-- BEGIN
example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
begin
  rw [add_mul, mul_sub, mul_sub],
  rw [add_sub, mul_comm b a, sub_add, sub_self, sub_zero],
  rw [← pow_two a, ← pow_two b],
end
-- END
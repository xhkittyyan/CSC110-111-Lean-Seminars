import data.real.basic

variables a b c : ℝ

#check mul_comm c 
#check mul_assoc c b a

-- BEGIN
example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm a,
  sorry,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw mul_comm, 
  sorry,
end
-- END
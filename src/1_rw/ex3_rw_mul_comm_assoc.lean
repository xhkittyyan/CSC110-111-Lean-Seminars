import data.real.basic

variables a b c : ℝ

#check mul_comm b a
#check mul_assoc c b a

-- BEGIN
example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  sorry,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  sorry,
end
-- END
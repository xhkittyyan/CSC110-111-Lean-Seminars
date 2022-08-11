import data.real.basic

variables a b c d e f : ℝ

#check mul_comm e
#check mul_assoc f c a
#check sub_self

-- BEGIN
example (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
   rw mul_assoc a b c,
   rw h, 
   rw mul_assoc a e f,
end

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw hyp',
  rw mul_comm a, 
  rw sub_self,
end
-- END
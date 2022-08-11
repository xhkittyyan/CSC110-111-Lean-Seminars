import data.real.basic

variables a b c d : ℝ

#check mul_comm d c
#check mul_assoc d c a
#check two_mul d
#check two_mul (a + d)

-- BEGIN

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a * d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp,
end
-- END
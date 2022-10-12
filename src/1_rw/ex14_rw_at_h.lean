import data.real.basic

variables a b c d : ℝ

#check mul_comm d c
#check mul_assoc d c a
#check two_mul d
#check two_mul (a + d)

-- BEGIN
/- The rewrite tactic affects only the goal. The notation rw t at h 
applies the rewrite t at hypothesis h. -/

example (a b c d : ℝ) (h : c = d * a + b) (h' : b = a * d) :
  c = 2 * a * d :=
begin
  rw h' at h,
  rw mul_comm d a at h,
  rw ← two_mul (a * d) at h,
  rw ← mul_assoc 2 a d at h,
  exact h,
end
-- END
import topology.metric_space.basic

variables {X : Type*} [metric_space X]
variables x y z : X

#check dist_self
#check dist_self y
#check dist_comm
#check dist_comm y x
#check dist_triangle 
#check dist_triangle x y z
#check two_mul
#check @le_trans
#check @div_le_div_of_le

-- BEGIN
example (x y : X) : 0 ≤ dist x y := 
begin 
  have h := dist_triangle x y x,
  /- have h : dist x x ≤ dist x y + dist y x -/
  rw dist_comm y x at h,
  linarith [dist_self x],
end

example (x y : X) : 0 ≤ dist x y := 
begin 
  have h := dist_triangle x y x,
  /- have h : dist x x ≤ dist x y + dist y x -/
  rw dist_comm y x at h,
  rw ← two_mul (dist x y) at h,
  rw dist_self at h,
  have h' : 0 / 2 ≤ (2 * dist x y) / 2 := div_le_div_of_le zero_le_two h,
  rw ← div_mul_eq_mul_div at h',
  norm_num at h',
  exact h',
end
-- END

import algebra.group

-- BEGIN

variables {G : Type*} [group G] 
variables a b c : G

#check one_mul 
#check mul_assoc
#check inv_mul_self
#check mul_left_inv
#check mul_right_cancel 
#check eq.symm
#check (one_mul b).symm
#check (mul_left_inv a).symm

namespace my_group

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  have h : a * a⁻¹ * a = 1 * a,
    rw mul_assoc,
    rw mul_left_inv a,
    rw mul_one,
    rw one_mul,
  apply mul_right_cancel h,
end

theorem mul_one (a : G) : a * 1 = a :=
begin
  rw ← mul_left_inv a,
  rw ← mul_assoc a,
  rw mul_right_inv a, 
  rw one_mul,
end

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  have h : (a * b)⁻¹ * a * b = b⁻¹ * a⁻¹ * a * b,
    rw mul_assoc b⁻¹ a⁻¹ a, 
    rw mul_left_inv a,
    rw mul_one b⁻¹,
    rw mul_left_inv b,
    rw mul_assoc (a * b)⁻¹ a b,
    rw mul_left_inv (a * b),
  rw mul_assoc at h,
  rw mul_assoc at h,
  apply mul_right_cancel h,
end 

/- Alternatively, starting with proving mul_cancel_left 
and mul_inv_left -/

theorem mul_cancel_left (a b c : G) (h : a * b = a * c) : b = c :=
begin
  rw ← one_mul b,
  rw ← one_mul c,
  rw ← mul_left_inv a,
  repeat {rw mul_assoc},
  rw h,
end

theorem mul_inv_left (a b c : G) (h : b = a⁻¹ * c) : a * b = c :=
begin
  apply mul_cancel_left a⁻¹,
  rw ← mul_assoc,
  rw mul_left_inv,
  rw one_mul,
  rw h,
end

example (a : G) : a * 1 = a :=
begin
  apply mul_inv_left,
  exact (mul_left_inv a).symm, /- it is eqivelant to 'rw mul_left_inv' -/
end

example (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_inv_left,
  rw mul_one a⁻¹, /- 'exact (mul_one a⁻¹).symm' works too -/
end

example (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_cancel_left (a * b),
  rw mul_right_inv,
  rw mul_assoc,
  rw ← mul_assoc b b⁻¹,
  rw mul_right_inv,
  rw one_mul,
  rw mul_right_inv,
end 

end my_group

#check mul_right_inv
#check mul_one
#check mul_inv_rev

-- END
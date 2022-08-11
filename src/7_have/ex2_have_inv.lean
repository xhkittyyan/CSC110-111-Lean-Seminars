import algebra.group

-- BEGIN

variables {G : Type*} [group G] 

#check one_mul 
#check mul_assoc
#check mul_left_inv
#check mul_right_cancel 

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

end my_group

-- END
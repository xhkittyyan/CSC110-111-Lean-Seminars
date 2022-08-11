import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

#check add_zero
#check zero_add
#check add_mul
#check add_right_cancel

-- BEGIN
theorem zero_mul (a : R) : 0 * a = 0 :=
begin 
  have h : 0 * a + 0 * a = 0 + 0 * a,
    { rw [← add_mul, add_zero,zero_add] },
  rw add_right_cancel h,
end
-- END

#check zero_mul

end my_ring
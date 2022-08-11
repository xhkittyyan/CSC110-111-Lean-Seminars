import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

#check add_zero
#check mul_add
#check add_left_cancel

-- BEGIN

theorem mul_zero (a : R) : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
    { rw [←mul_add, add_zero, add_zero] },
  rw add_left_cancel h,
end
-- END

#check mul_zero

end my_ring
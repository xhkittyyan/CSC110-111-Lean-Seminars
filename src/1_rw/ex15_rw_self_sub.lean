import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]
variables a b c : R

#check add_right_neg
#check sub_eq_add_neg 
#check sub_eq_add_neg c

-- BEGIN
theorem self_sub (a : R) : a - a = 0 :=
begin
  rw sub_eq_add_neg a,
  rw add_right_neg,
end
-- END

#check self_sub

end my_ring
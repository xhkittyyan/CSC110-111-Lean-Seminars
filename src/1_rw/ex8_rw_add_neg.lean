import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

#check add_zero
#check add_assoc
#check add_right_neg

-- BEGIN
theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a :=
begin
  sorry,
end
-- END

end my_ring
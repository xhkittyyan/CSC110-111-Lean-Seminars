import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]
variables a b c : R

#check zero_add 
#check zero_add c
#check add_zero
#check add_zero b
#check add_comm 
#check add_comm c
#check add_assoc
#check add_right_neg
#check add_right_neg b

-- BEGIN
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
begin
  rw [← zero_add b, ← zero_add c, ← add_right_neg a],
  rw [add_comm a, add_assoc, h, ← add_assoc],
end

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
begin
  rw [← add_zero a, ← add_zero c, ← add_right_neg b],
  sorry,   
end
-- END

#check @add_left_cancel
#check @add_right_cancel

end my_ring
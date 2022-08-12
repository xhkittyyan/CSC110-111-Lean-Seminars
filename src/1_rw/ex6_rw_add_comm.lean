import algebra.ring

#check add_comm
#check zero_add
#check add_left_neg 

namespace my_ring

variables {R : Type*} [ring R]

theorem add_zero (a : R) : a + 0 = a :=
begin 
 rw add_comm,
 rw zero_add,
end

/- A shorter proof -/
example (a : R) : a + 0 = a :=
by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 :=
begin 
  sorry,
end

end my_ring

#check add_zero
#check add_right_neg
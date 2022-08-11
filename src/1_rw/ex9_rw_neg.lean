import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]
variables a b c : R

#check zero_add
#check add_zero c
#check add_comm c a 
#check add_assoc a 
#check add_right_neg c
#check add_left_neg 

-- BEGIN
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
begin
  rw ← add_zero b,
  rw ← add_right_neg a, 
  rw ← add_assoc b, 
  rw add_comm b a,
  rw h,
  rw zero_add,
end

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
begin
 rw ← add_zero a,
 rw ← add_right_neg b,
 rw ← add_assoc a,
 sorry,
end

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero,
end

theorem neg_neg (a : R) : -(-a) = a :=
begin 
  apply neg_eq_of_add_eq_zero,
  sorry,
end

-- END

#check @neg_eq_of_add_eq_zero
#check neg_zero
#check neg_neg 

end my_ring
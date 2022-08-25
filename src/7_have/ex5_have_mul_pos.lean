import algebra.order.ring

#check sub_nonneg
#check sub_mul

variables {R : Type*} [ordered_ring R]
variables a b c : R

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := 
begin
  rw ← sub_nonneg,
  rw ← sub_mul,
  have h'' : 0 ≤ b - a := sub_nonneg.2 h,
  exact mul_nonneg h'' h',
end
import algebra.order.ring

variables {R : Type*} [ordered_ring R]
variables a b c : R

/- NOTE: No `by_cases` used. May need to relocate. -/

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := 
begin
  rw ← sub_nonneg,
  rw ← sub_mul,
  have h'' : 0 ≤ b - a := sub_nonneg.2 h,
  exact mul_nonneg h'' h',
end
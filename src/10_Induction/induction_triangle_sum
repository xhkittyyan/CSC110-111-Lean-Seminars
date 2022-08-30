Import tactics
import data.real.basic

example (n : ℕ) : 2 * triangle_sum n = n * (n+1) :=
begin 
  induction n with k h_ih,
  { unfold triangle_sum,
    rw sum_range_one,
    norm_num, },
  { unfold triangle_sum at *,
    rw sum_range_succ,
    rw mul_add,
    rw h_ih,
    rw succ_eq_add_one,
    ring, },
end 

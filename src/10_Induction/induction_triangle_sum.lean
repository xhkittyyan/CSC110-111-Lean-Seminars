import data.real.basic

open nat 

theorem sum_id (n : ℕ) : Σ i in range (n + 1), i = n * (n + 1) / 2 :=
begin
  symmetry, 
  apply nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2),
  induction n with n ih,
   { simp },
  rw [finset.sum_range_succ, mul_add 2, ←ih, nat.succ_eq_add_one],
  ring,
end

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

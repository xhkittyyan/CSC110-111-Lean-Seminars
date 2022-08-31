import data.real.basic

open nat 

lemma succ_mul (a b : ℕ) : succ a * b = a * b + b :=
begin
  induction b with d hd,
  { rw mul_zero,
    rw mul_zero, },
  { rw mul_succ,
    rw mul_succ,
    rw hd,
    rw add_succ,
    rw add_succ,
    rw add_right_comm, }
end


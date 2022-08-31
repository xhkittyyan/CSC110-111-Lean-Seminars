import data.real.basic

open nat 
#check mul_zero
#check mul_succ
#check add_succ
#check add_right_comm

lemma succ_mul (a b : ℕ) : succ a * b = a * b + b :=
begin
  induction b with d hd,
  { sorry, },
  { rw mul_succ,
    rw mul_succ,
    rw hd,
    sorry, },
end


import data.real.basic

open nat

#check add_succ

example (n : ℕ) : 0 + n = n :=
begin
  induction n with n ih,
    norm_num,
  rw add_succ, 
  rw ih,
end



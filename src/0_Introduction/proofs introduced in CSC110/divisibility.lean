import tactic 
open nat 

variables {n d t : ℕ} 
#check one_mul
#check @le_self_mul 

example (n : ℕ) : (1 ∣ n) :=
begin
  cases n with d hd,
  { norm_num,},
  { use d + 1,
  rw one_mul, }
end 

example : ∀ n d : ℤ, ∃ k : ℤ, n = d * k → d ≤ n := 
begin
  intros n d,
  use 1,
  intro hdn,
  rw hdn,
  rw mul_one,
end

example : ∀ n d : ℤ, d ∣ n → d ≤ n := 
begin
  intros n d,
  intro hdn,
  cases hdn with t ht,
  rw ht,
  exact le_self_mul,
end 


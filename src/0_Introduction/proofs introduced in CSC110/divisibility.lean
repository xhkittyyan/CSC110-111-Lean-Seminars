import tactic 
open nat 

variables {n d : ℤ} 
#check one_mul
#check @le_self_mul 

example : (1 ∣ n) :=
begin
  use n,
  rw one_mul,
end

example (hn : n > 0) (hd : d > 0): d ∣ n → d ≤ n := 
begin
  intro hdn,
  rcases hdn with ⟨k, rfl⟩,
  nth_rewrite_lhs 0 ← mul_one d,
  apply mul_le_mul,
  exact le_refl d,
  {
    rcases lt_trichotomy k 0 with hk | rfl | hk;
    nlinarith,
  },
  exact zero_le_one,
  exact le_of_lt hd,
end

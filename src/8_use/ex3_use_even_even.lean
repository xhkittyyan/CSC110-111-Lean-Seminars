import data.nat.parity
import data.real.basic

#check mul_left_comm

/- Tactic proofs -/
example : ∀ m n : nat, even n → even (m * n) :=
begin
  intros m n hn,
  cases hn with k hk,
  use m * k,
  sorry, 
end 

example : ∀ m n : nat, even n → even (m * n) :=
begin
  rintro m n ⟨k, hk⟩,
  use m * k,
  sorry, 
end 

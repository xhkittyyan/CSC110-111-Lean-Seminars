import data.nat.basic
import data.real.basic

#check mul_left_comm

/- A term proof -/
example : ∀ m n : nat, even n → even (m * n) :=
  assume m n ⟨k, (hk : n = 2 * k)⟩,
  have hmn : m * n = 2 * (m * k),
    by rw [hk, mul_left_comm],
  show ∃ l, m * n = 2 * l,
    from ⟨_, hmn⟩

/- Tactic proofs -/
example : ∀ m n : nat, even n → even (m * n) :=
begin
  intros m n hn,
  cases hn with k hk,
  use m * k,
  rw hk,
  rw mul_left_comm, 
end 

example : ∀ m n : nat, even n → even (m * n) :=
begin
  rintro m n ⟨k, hk⟩,
  use m * k,
  rw hk,
  rw mul_left_comm, 
end 
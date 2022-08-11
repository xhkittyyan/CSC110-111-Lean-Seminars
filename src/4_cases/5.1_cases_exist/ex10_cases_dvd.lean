import tactic

-- BEGIN

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  cases h with hmn hmk,
  cases hmn with a ha,
    rw ha,
    rw mul_assoc,
    apply dvd_mul_right,
  cases hmk with b hb,
    rw hb,
    rw mul_comm, 
    rw mul_assoc,
  apply dvd_mul_right,
end


-- END


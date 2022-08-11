import tactic

-- BEGIN
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right,
end

/- Using the cases tactic -/
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


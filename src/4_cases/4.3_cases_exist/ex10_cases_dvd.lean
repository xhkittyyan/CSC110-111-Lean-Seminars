import tactic

#check dvd_mul_right

-- BEGIN

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  cases h with hmn hmk,
    /- deconstruct the disjunction m ∣ n ∨ m ∣ k -/
  cases hmn with a ha,
    /- instantiate the existential quantifier a in ha -/
    rw ha,
    rw mul_assoc,
    apply dvd_mul_right,
  cases hmk with b hb,
    /- instantiate the existential quantifier b in hb -/
    rw hb,
    rw mul_comm, 
    rw mul_assoc,
  apply dvd_mul_right,
end

-- END


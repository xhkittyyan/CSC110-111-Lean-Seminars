import number_theory.basic
import data.nat.totient
import data.nat.pow
import field_theory.finite.basic

open nat

def encrypt (e n m : ℕ) := m ^ e % n
def decrypt (d n m : ℕ) := m ^ d % n

theorem RSA_correct (n d e m : ℕ) (h₁ : ∃ k : ℕ, e * d = n.totient * k + 1) (h₂ : m.coprime n) :
  decrypt d n (encrypt e n m) ≡ m [MOD n] :=
begin
  rw [encrypt, decrypt],
  rw ← pow_mod,
  rw ← pow_mul,
  apply modeq.trans (mod_modeq _ _),
  cases h₁ with k h,
  rw h,
  rw [pow_add, pow_mul, pow_one],
  suffices h' : (m ^ n.totient) ^ k ≡ 1 [MOD n],
  { nth_rewrite_rhs 0 ← one_mul m,
    exact modeq.mul_right m h', },
  { rw ← one_pow k,
    apply modeq.pow,
    exact modeq.pow_totient h₂, }
end

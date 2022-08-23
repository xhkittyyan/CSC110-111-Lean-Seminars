import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s : ℕ → ℝ} {a : ℝ}

-- BEGIN
theorem exists_abs_le_of_converges_to (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n hn,
  specialize h n hn,
  have t := abs_sub_abs_le_abs_sub (s n) a,
  have t' := lt_of_le_of_lt t h,
  exact sub_lt_iff_lt_add'.mp t',
end
-- END
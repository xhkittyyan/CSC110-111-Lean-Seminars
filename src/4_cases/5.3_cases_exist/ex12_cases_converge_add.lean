import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

-- BEGIN
variables {s t : ℕ → ℝ} {a b : ℝ}

#check sub_sub (a + b) 

theorem converges_to_add
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, 
  dsimp,
  have ε2pos : 0 < ε / 2,
  { linarith },
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  use max Ns Nt,
  intros n hn,
  specialize hs n (le_trans (le_max_left Ns Nt) hn),
  specialize ht n (le_trans (le_max_right Ns Nt) hn),
  rw (by ring : s n + t n - (a + b) = (s n - a) + (t n - b)),
  rw ← add_halves ε,
  have triangle := abs_add (s n - a) (t n - b),
  have lt_two_half_ε := add_lt_add hs ht,
  exact lt_of_le_of_lt triangle lt_two_half_ε,
end
-- END
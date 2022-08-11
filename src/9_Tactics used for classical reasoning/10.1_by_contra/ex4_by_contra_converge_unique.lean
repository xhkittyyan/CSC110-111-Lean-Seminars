import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

open_locale classical

#check @half_pos
#check @abs_sub_comm
#check @abs_sub_le
#check @add_halves

-- BEGIN
theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0 := abs_pos.mpr (sub_ne_zero_of_ne abne),
  let ε := abs (a - b) / 2,
  have εpos : ε > 0 := half_pos this,
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε := hNa N (le_max_left Na Nb),
  have absb : abs (s N - b) < ε := hNb N (le_max_right Na Nb),
  have : abs (a - b) < abs (a - b),
  { nth_rewrite 1 (by simp : |a - b| = ε + ε),
    -- OR: nth_rewrite 1 ← add_halves (abs (a - b)),
    rw abs_sub_comm at absa,
    linarith only [absa, absb, abs_sub_le a (s N) b], },
  exact lt_irrefl _ this
end
-- END
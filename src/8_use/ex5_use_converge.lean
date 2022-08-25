import data.real.basic

/- Tactics you may consider
-intros
-rw
-apply
-exact
-use
-/

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variable (a : ℝ)

-- BEGIN
theorem converges_to_const : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  sorry,
end
-- END
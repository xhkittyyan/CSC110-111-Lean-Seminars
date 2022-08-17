import data.real.basic

#check sub_self
#check abs_zero

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε epos,
  dsimp,
  rw sub_self,
  norm_num, 
  use 0, 
  intros n nge,
  exact epos, 
end

example (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε epos,
  use 0,
  intros n nge,
  dsimp,
  rw sub_self,
  rw abs_zero,
  apply epos,
end

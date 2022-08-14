import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s : ℕ → ℝ} {a : ℝ}

-- BEGIN

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

#check converges_to_const
#check abs_pos
#check abs_pos.mp
#check abs_pos.mpr

theorem converges_to_mul_const
    {c : ℝ} (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
  intros ε εpos,
  let ε' := ε / |c|,
  have ε'pos : ε' > 0 := div_pos εpos acpos,
  dsimp,
  cases (cs (ε / |c|) ε'pos) with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw ← mul_sub,
  rw abs_mul,
  exact (lt_div_iff' acpos).mp hN,
end
-- END
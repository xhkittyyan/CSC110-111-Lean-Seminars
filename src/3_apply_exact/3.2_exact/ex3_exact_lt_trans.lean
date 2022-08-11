import tactic
import data.real.basic

/- Tacics you may consider
-intro
-rw
-apply
-exact
-cases
-rcases
-split
-contrapose!
-push_neg
-/

#check le_trans
#check lt_trans
#check @lt_iff_le_not_le

-- BEGIN
variables {α : Type*} [preorder α]
variables a b c : α

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  push_neg,
  intro h, 
  exact h,
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  intros h h',
  cases h with h1 h2,
  cases h' with h'1 h'2,
  split,
  apply le_trans h1 h'1,
  contrapose! h'2,
  apply le_trans h'2,
  exact h1,
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  intro z,
  cases z with z hz,
  cases hz with xltz zlty,
  exact lt_trans xltz zlty,
end

/- Alternatively, using the rcases tactic leads to a shorter proof -/
example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  exact lt_trans xltz zlty,
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty
-- END
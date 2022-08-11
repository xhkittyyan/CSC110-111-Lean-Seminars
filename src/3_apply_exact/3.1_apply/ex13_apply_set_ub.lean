variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

/- Tactics you may consider
-intro
-apply
-exact
-have
-/

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
begin
  intros x xs,
  have h1: x ≤ a,
    apply h,
    exact xs,
  apply le_trans h1 h',
end
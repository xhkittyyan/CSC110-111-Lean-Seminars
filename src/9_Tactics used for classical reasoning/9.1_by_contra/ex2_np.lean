variables {α : Type*} (P : α → Prop)

/- Tactics you may consider
-intro
-exact
-apply
-by_contra
-/

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
begin 
  intro x,
  by_contra h',
  exact h ⟨x, h'⟩,
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  intro h,
  cases h with x p,
  exact h x p,
end

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contra h',
  apply h,
  intro x,
  show P x,
  by_contra h'',
  exact h' ⟨x, h''⟩, 
end

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
begin
  intro h',
  cases h with x np,
  exact np (h' x),
end
import data.set.basic
/- 
Tactics you may consider 
-intro(s)
-apply
-exact
-/

variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  intros rs st x xr,
  apply st,
  apply rs,
  exact xr,
end

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := 
begin
  intros rs st x xr,
  exact st (rs xr), 
end

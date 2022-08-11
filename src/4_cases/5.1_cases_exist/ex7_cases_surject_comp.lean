import tactic

open function

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

-- BEGIN
example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
  intro z,
  dsimp, 
  cases surjg z with y h1,
  cases surjf y with x h2,
  use x,
  rw h2,
  rw h1,
end
-- END
import data.real.basic

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}
variables a b c : ℝ

#check add_left_inj 
#check add_left_inj b 
#check @mul_right_inj
#check @mul_right_inj'

open function

-- BEGIN

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  exact (add_left_inj c).mp h',
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
  intros x₁ x₂ h1,
  exact (mul_right_inj' h).mp h1,
end

example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) :=
begin
  intros x₁ x₂ h,
  dsimp at h,
  apply injf,
  apply injg,
  exact h,
end

-- END
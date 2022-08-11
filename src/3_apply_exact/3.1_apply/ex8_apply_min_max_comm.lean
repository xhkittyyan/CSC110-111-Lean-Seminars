import data.real.basic

variables a b : ℝ

#check le_antisymm
#check le_min
#check min_le_left
#check min_le_right

-- BEGIN
example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end

example : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end

example : max a b = max b a :=
begin
  apply le_antisymm,
  { show max a b ≤ max b a,
    apply max_le,
      apply le_max_right, 
      apply le_max_left },
  { show max b a ≤ max a b, 
    apply max_le,
      apply le_max_right,
      apply le_max_left },
end

-- END
import data.real.basic

variables a b c : ℝ

#check add_le_add_left
#check add_le_add_right
#check le_antisymm
#check le_min
#check min_le_left
#check min_le_right

-- BEGIN

lemma aux : min a b + c ≤ min (a + c) (b + c) :=
begin
  apply le_min,
   show min a b + c ≤ a + c,
    have h : min a b ≤ a,
    apply min_le_left,
    apply add_le_add_right h, 
   show min a b + c ≤ b + c,   
    have h' : min a b ≤ b,
    apply min_le_right, 
    apply add_le_add_right h',
end

example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  exact aux a b c,
  have ha : min (a + c) (b + c) - c <= a := by linarith [min_le_left (a + c) (b + c)],
  have hb : min (a + c) (b + c) - c <= b := by linarith [min_le_right (a + c) (b + c)],
  have h : min (a + c) (b + c) - c <= min a b := le_min ha hb,
  linarith only [h],
end
-- END
import data.zmod.defs
import data.zmod.basic

#check zmod.fintype 6
#check (zmod.fintype 6).elems
#eval (zmod.fintype 6).elems

lemma zmod_6_elems_eq_0_to_5 : (zmod.fintype 6).elems = {0, 1, 2, 3, 4, 5} := begin
  refl,
end

lemma eq_val_of_eq_zmod { n : ℕ } {a b : zmod n} (h : a = b) : a.val = b.val := begin
  rw h,
end

example (p : ℕ) (h₁ : prime p) (h₂ : p > 3) : p % 6 = 1 ∨ p % 6 = 5 := begin
  have h : (p : zmod 6) ∈ ({0, 1, 2, 3, 4, 5} : finset (zmod 6)),
  {
    rw ← zmod_6_elems_eq_0_to_5,
    apply (zmod.fintype 6).complete,
  },
  simp at h,
  rcases h with (_|_|_|_|_|_);
  have h' := eq_val_of_eq_zmod h;
  rw zmod.val at h';
  norm_num at h',
  {
    exfalso,
    sorry,
  },
  {
    exact or.inl h',
  },
  {
    sorry,
  },
  {
    sorry,
  },
  {
    sorry,
  },
  {
    sorry,
  },
end

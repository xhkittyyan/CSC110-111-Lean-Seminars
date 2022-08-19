open classical 

variables A B P Q: Prop

/- Tactics you may consider
-intro
-exact
-apply
-split
-by_contra
-/

example (A B : Prop) : (A → B) ↔ (¬ B → ¬ A) := 
begin
    split,
    intros hab nb,
        sorry,  
    intros hnba ha,
        sorry, 
end

/- Alternatively, a term proof -/
#check @classical.by_contradiction
#check @classical.by_contradiction A

example (A B : Prop) : (A → B) ↔ (¬ B → ¬ A) := 
have h1 : (A → B) → (¬ B → ¬ A), from 
    (assume g : A → B, 
    assume n : ¬ B, 
    assume a: A,
    have b : B, from g a,
    show false, from n b),
have h2 : (¬ B → ¬ A) → (A → B), from 
    (assume g : ¬ B → ¬ A, 
    assume a : A, 
    show B, from by_contradiction
        (assume n : ¬ B, 
        have m : ¬ A, from g n,
        show false, from m a) ), 
show (A → B) ↔ (¬ B → ¬ A), from iff.intro h1 h2



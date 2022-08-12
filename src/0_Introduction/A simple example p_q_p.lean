import data.real.basic

example : ∀ P Q : Prop, P → Q → P := 

/- In Lean, the implication arrow → is right-associative. 
  P → Q → P in fact refers to P → (Q → P). -/

/- A paper-pencil proof of P → (Q → P) would be the following:
  - let P and Q be propositions;
  - assume that the hypothesis of P (hp) and the hypothesis of Q (hq)are true;
  - to prove P, we use hypothesis hp. -/

/- A Lean proof-/
begin 
  intros P Q, 
  /- The 'intros P Q' tactic introduces two free variables P and Q in the local 
  context. The tactic mimics how mathematicians work on paper: To prove a 
  universally quantified proposition, it suffices to prove it for some arbitrary 
  but fixed value of the bound variable. -/

  intros hp hq,
  /- The 'intros hp hq' tactic introduces the proof of P called hp and 
  the proof of Q called hq to the local context. In other words, we assume that 
  P is true and Q is true, and we want to prove P is true. Indeed, to prove an 
  implication, it suffices to take its left-hand side as the hypothesis and prove 
  its right-hand side true. -/
  
  exact hp,
  /- hp suffices to prove P because hp is the proof of P. The 'exact hp' tactic 
  tells Lean that hp is exactly needed to achieve and close the goal. -/
end
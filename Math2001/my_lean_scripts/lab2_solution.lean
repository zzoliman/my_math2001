-- (P ∨ (Q → P)) ∧ Q ⊢ P

example {P Q : Prop} (h : (P ∨ (Q → P)) ∧ Q) : P := 
  have h1 : P ∨ (Q → P) := And.left h 
  have h2 : Q := And.right h 
  by cases h1 with 
    | inl l => apply l
    | inr r => apply r h2

--=======================================================================================

-- P → Q, ¬Q ⊢ ¬P

example {P Q : Prop} (h1 : P → Q) (h2 : ¬Q) : ¬P := 
  have notp : ¬P := by 
    intros p 
    have q : Q := h1 p 
    apply h2 q 
  by apply notp

--Alternate proof:  since we only apply notp, we can omit constructing it and putting
--                  it into the context

example {P Q : Prop} (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  intros p 
  have q : Q := h1 p 
  apply h2 q 
  
--========================================================================================

-- P ⊢ ¬¬P

example {P : Prop} (h : P) : ¬¬P := 
  have notnotp : ¬¬P := by 
    intros notp 
    apply notp h 
  by apply notnotp 

-- Alternate proof:  same reasoning as above

example {P : Prop} (h : P) : ¬¬P := 
  have notnotp : ¬¬P := by 
    intros notp 
    apply notp h 
  by apply notnotp 
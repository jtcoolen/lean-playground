namespace Kleene

variable (p : String → Prop)

inductive Star : String → Prop where
  | Empty : Star ""
  | Iter : ∀ s₁ s₂, p s₁ → Star s₂ → Star (s₁ ++ s₂)

end Kleene

#check @Kleene.Star
#check id

inductive Regexp : (String → Prop) → Type where
  | Char : ∀ c : Char, Regexp (fun s =>  s = String.singleton c)
  | Concat : ∀ p₁ p₂ : String → Prop, ∀ _ : Regexp p₁, ∀ _ : Regexp p₂,
      Regexp (fun s => ∃ s₁ s₂, s = s₁ ++ s₂ ∧ p₁ s₁ ∧ p₂ s₂)
  | Or : ∀ p₁ p₂ : String → Prop, Regexp (fun s => p₁ s ∨ p₂ s)
  | Star : ∀ p : String → Prop, Regexp (fun s => Kleene.Star p s)

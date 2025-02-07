variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨ h.right, h.left ⟩, fun h => ⟨ h.right, h.left ⟩ ⟩

example : p ∨ q ↔ q ∨ p :=
  ⟨ fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl ⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨ fun h => ⟨ h.left.left, ⟨ h.left.right, h.right ⟩ ⟩,
  fun h => ⟨ ⟨ h.left, h.right.left ⟩, h.right.right ⟩ ⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨ fun h => h.elim
    (fun h1 => h1.elim Or.inl (Or.inr ∘ Or.inl))
    (Or.inr ∘ Or.inr),
  fun h => h.elim
    (Or.inl ∘ Or.inl)
    (fun h1 => h1.elim (Or.inl ∘ Or.inr) Or.inr) ⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨ fun h => h.right.elim
    (fun hq => Or.inl (And.intro h.left hq))
    (fun hr => Or.inr (And.intro h.left hr)),
  fun h => h.elim
    (fun h1 => And.intro h1.left (Or.inl h1.right))
    (fun h1 => And.intro h1.left (Or.inr h1.right)) ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨ fun h => h.elim
    (fun hp => And.intro (Or.inl hp) (Or.inl hp))
    (fun hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right)),
  fun h => h.left.elim
    (fun hp => h.right.elim Or.inl (fun _ => Or.inl hp))
    (fun hq => h.right.elim Or.inl (fun hr => (Or.inr (And.intro hq hr))))
  ⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨ fun h hpq => h hpq.left hpq.right,
  fun h hp hq => h (And.intro hp hq) ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨ fun h => And.intro (h ∘ Or.inl) (h ∘ Or.inr),
  fun h h1 => h1.elim h.left h.right ⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨ fun h => And.intro
    (fun h' => False.elim (h (Or.inl h')))
    (fun h' => False.elim (h (Or.inr h'))),
  fun h h' => h'.elim
    (fun hp => False.elim (h.left hp))
    (fun hq => False.elim (h.right hq)) ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h h' => h.elim
    (fun hnp => False.elim (hnp h'.left))
    (fun hnq => False.elim (hnq h'.right))

example : ¬(p ∧ ¬p) := fun h => absurd h.left h.right
example : p ∧ ¬q → ¬(p → q) := fun h h' => absurd (h' h.left) h.right
example : ¬p → (p → q) := fun hnp hp => False.elim (hnp hp)
example : (¬p ∨ q) → (p → q) := fun h hp => h.elim (fun hnp => False.elim (hnp hp)) id
example : p ∨ False ↔ p := ⟨ fun h => h.elim id False.elim, Or.inl ⟩
example : p ∧ False ↔ False := ⟨ fun h => h.right, False.elim ⟩
example : (p → q) → (¬q → ¬p) := fun h hnq hp => absurd (h hp) hnq

open Classical

variable (p q r : Prop)

#check em

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := em p
example : (((p → q) → p) → p) := sorry

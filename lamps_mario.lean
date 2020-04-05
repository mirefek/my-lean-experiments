import logic.function
import data.fintype

def list.chain'' {α} (R : α → α → Prop) : (α → Prop) → list α → α → Prop
| P [] a := P a
| P (a::l) b := P a ∧ list.chain'' (R a) l b

def flip_one {α} [decidable_eq α] (f : α → bool) (i : α) : α → bool :=
function.update f i (bnot (f i))

def admissible {α} [decidable_eq α] (f g : α → bool) : Prop :=
∃ i, g = flip_one f i

def restricted_admissible {α} [decidable_eq α] (f g : α ⊕ α → bool) : Prop :=
∃ i, g = flip_one f (sum.inl i)

def end_state {α} : α ⊕ α → bool
| (sum.inl _) := tt
| (sum.inr _) := ff

def lamp_seq {α} (R : ∀ (f g : α ⊕ α → bool), Prop) (l : list (α ⊕ α → bool)) : Prop :=
list.chain'' R (λ s, end_state = s) l (λ _, ff)

open_locale classical
theorem C4 {α} [fintype α] [decidable_eq α] (k n : ℕ)
  (h1 : 2 ∣ k + n) (h2 : n ≤ k) (h3 : fintype.card α = n) :
  fintype.card {f : vector (α ⊕ α → bool) k // lamp_seq admissible f.1} =
  2 ^ (k - n) *
  fintype.card {f : vector (α ⊕ α → bool) k // lamp_seq restricted_admissible f.1} :=
sorry

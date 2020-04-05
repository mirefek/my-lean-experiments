import tactic
import data.fin
universes u v

variables {n : ℕ} {α : Type u} {β : Type v}

lemma fold_step (a1 : array n α) (a2 : array n.succ α) (b : β) (f : α → β → β)
  : (∀ i : fin n, a1.read i = a2.read ⟨i, nat.lt.step i.is_lt⟩) →
    a2.foldl b f = f (a2.read ⟨n, lt_add_one n⟩) (a1.foldl b f)
:=
begin
  intros,
  induction n with n n_ih,  
  sorry
end

def array.simple_take (a : array n α) (m : nat) (h : m ≤ n) : array m α :=
  ⟨λ i : fin m, a.read ⟨i.val, lt_of_lt_of_le i.is_lt h⟩⟩
def foldl_inits (a : array n α) (b : β) (f : α → β → β) (k : ℕ) (h : k ≤ n) : β
  := (a.simple_take k h).foldl b f
lemma foldl_inits_eq
  (a : array n α) (b : β) (f : α → β → β) (f2 : Π (k : ℕ), k ≤ n → β)
  : f2 0 bot_le = b →
    (∀ i : fin n,
      f2 i.val.succ i.is_lt = f (a.read i) (f2 i.val (le_of_lt i.is_lt))) →
  f2 = foldl_inits a b f
:=
begin
  intros,
  apply funext, assume (k : ℕ),
  apply funext, assume (kn_le : k ≤ n),
  induction k with k k_ih,
  show f2 0 bot_le = foldl_inits a b f 0 bot_le, from a_1,
  let pref1 := a.simple_take k (le_of_lt kn_le),
  let pref2 := a.simple_take k.succ kn_le,
  apply eq.trans,
  have : f2 (nat.succ k) kn_le = f (a.read ⟨k, kn_le⟩) (pref1.foldl b f), begin
    apply eq.trans (a_2 ⟨k, kn_le⟩),
    congr,
    exact k_ih (le_of_lt kn_le),
  end,
  exact this,
  have : f (a.read ⟨k, kn_le⟩) (pref1.foldl b f) = pref2.foldl b f, begin
    have : a.read ⟨k, kn_le⟩ = pref2.read ⟨k, lt_add_one k⟩, from rfl,
    rw this,
    have : ∀ (i : fin k), pref1.read i = pref2.read ⟨i.val, nat.lt.step i.is_lt⟩, begin
      intros,
      exact rfl,
    end,
    show f (pref2.read ⟨k, lt_add_one k⟩) (pref1.foldl b f) = pref2.foldl b f,
      from (fold_step pref1 pref2 b f this).symm,
  end,
  exact this,
end

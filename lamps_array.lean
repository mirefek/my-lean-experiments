import tactic
import tactic.norm_cast
import data.rat
import data.fintype
import data.real.basic

noncomputable theory
open_locale classical

/---  problem statement  ---/

def lamp_switch_seq (n k : ℕ) := array k (fin (n+n))
--local attribute [instance] classical.prop_decidable

instance (n k : ℕ) : has_mem (fin (n+n)) (lamp_switch_seq n k) := array.has_mem
instance (n k : ℕ) : fintype (lamp_switch_seq n k) :=
begin
  unfold lamp_switch_seq,
  apply_instance
end

def lamp_state (n : ℕ) := array (n+n) bool

def ini_state (n : ℕ) : (lamp_state n) := ⟨λ i : fin (n+n), ff⟩
def target_state (n : ℕ) : (lamp_state n) := ⟨λ i : fin (n+n), (i:ℕ) < n⟩
def switch_lamp {n : ℕ} (i : fin (n+n)) (s1 : lamp_state n) : lamp_state n
:= s1.write i (¬s1.read i)
-- := ⟨λ j : fin (n+n), xor (i = j) (s1.read j)⟩

def fin_state {n k : ℕ} (seq : lamp_switch_seq n k) : lamp_state n
  := seq.foldl (ini_state n) switch_lamp

def is_N_seq {n k : ℕ} (seq : lamp_switch_seq n k) : Prop
  := (fin_state seq = target_state n)
def is_M_seq {n k : ℕ} (seq : lamp_switch_seq n k) : Prop
  := is_N_seq seq ∧ ∀ l ∈ seq, (l : ℕ) < n

def N_seq (n k : ℕ) := @subtype (lamp_switch_seq n k) is_N_seq
def M_seq (n k : ℕ) := @subtype (lamp_switch_seq n k) is_M_seq

instance (n k : ℕ) : fintype (N_seq n k) := by apply subtype.fintype
instance (n k : ℕ) : fintype (M_seq n k) := by apply subtype.fintype

def N_num (n k : ℕ) := fintype.card (N_seq n k)
def M_num (n k : ℕ) := fintype.card (M_seq n k)

/- The statement of the theorem -/

-- TODO!!! it should be also stated that k, n are of the same parity, otherwise it is false

def lamp_prop : Prop :=
  ∀ n k : ℕ, 0 < n → n ≤ k →
    (N_num n k : ℚ) / (M_num n k) = 2^(k-n)

/- Proof -/

def to_fin_2n_small {n : ℕ} (i : fin n) : fin (n+n)
  := ⟨i, nat.lt_add_left i.val n n i.is_lt⟩
def to_fin_2n_big {n : ℕ} (i : fin n) : fin (n+n)
  := ⟨i+n, add_lt_add_right i.is_lt n⟩

def is_D_seq {n k : ℕ} (seq : lamp_switch_seq n k) : Prop
  :=
  let fs := fin_state seq in
  ∀ i : fin n, xor (fs.read  (to_fin_2n_small i)) (fs.read (to_fin_2n_big i))
def D_seq (n k : ℕ) := @subtype (lamp_switch_seq n k) is_D_seq
instance (n k : ℕ) : fintype (D_seq n k) := by apply subtype.fintype
def D_num (n k : ℕ) := fintype.card (D_seq n k)

lemma N_num_by_D_num (n k : ℕ) : (N_num n k) * 2^n = (D_num n k)
:=
begin
  sorry
end

lemma M_num_by_D_num (n k : ℕ) : (M_num n k) * 2^k = (D_num n k)
:=
begin
  sorry
end

-- proving that M ≠ 0

def nontriv_val_small {n k : ℕ} {i : fin k} (c : i.val < n) : fin (n+n) :=
  ⟨i, nat.lt_add_left i.val n n c⟩
def nontriv_val_big {n k : ℕ} {i : fin k} (n_pos : 0 < n) (c : ¬i.val < n) : fin (n+n) :=
  ⟨0, nat.lt_add_left 0 n n n_pos⟩
def nontriv_seq (n k : ℕ) (n_pos : 0 < n) : lamp_switch_seq n k :=
  ⟨λ i : fin k,
    dite (i.val < n)
      nontriv_val_small
      (nontriv_val_big n_pos)
  ⟩

lemma nontriv_correct (n k : ℕ) (n_pos : 0 < n)
  : is_N_seq (nontriv_seq n k n_pos)
:=
begin
  sorry
end

lemma nontriv_all_small (n k : ℕ) (n_pos : 0 < n)
  : ∀ l ∈ (nontriv_seq n k n_pos), ↑l < n
:=
begin
  let seq := nontriv_seq n k n_pos,
  show ∀ l ∈ seq, ↑l < n,
  intros,
  obtain ⟨si, hs⟩ : ∃ si, seq.data si = l, from H,
  rw ←hs,
  cases classical.em (si.val < n) with si_small si_big,
  -- si_small
  have : seq.data si = nontriv_val_small si_small, from dif_pos si_small,
  rw this,
  show si.val < n, from si_small,
  -- si_big
  have : seq.data si = nontriv_val_big n_pos si_big, from dif_neg si_big,
  rw this,
  show 0 < n, from n_pos,  
end

lemma fintype.card_pos (α : Type) [ft : fintype α] (x : α)
  : 0 < fintype.card α
:= begin
  apply finset.card_pos.2,
  apply exists.intro,
  show α, from x,
  show x ∈ finset.univ, from finset.mem_univ x
end

lemma M_num_nontriv {n k : ℕ} (n_pos : 0 < n) (nk_le : n ≤ k)
  : M_num n k > 0
:=
begin
  let seq : lamp_switch_seq n k := (nontriv_seq n k n_pos),
  have : is_M_seq seq, begin
    apply and.intro,
    show is_N_seq seq, by apply nontriv_correct,
    show ∀ l ∈ seq, ↑l < n, by apply nontriv_all_small,
  end,
  apply fintype.card_pos,
  show M_seq n k, from ⟨seq, this⟩
end

-- final arithmetics

lemma lamp_arith (M N D n k : ℕ) (h1 : N * 2^n = D) (h2 : M * 2^k = D)
  (non_triv : M > 0) (nk_le : n ≤ k) :
  (N / M : ℚ) = 2^(k-n) :=
begin
  rw div_eq_iff_mul_eq,
  rw ← domain.mul_left_inj (ne_of_gt $ pow_pos two_pos n : (2^n : ℚ) ≠ 0),
  rw [← mul_assoc, ← pow_add, nat.add_sub_cancel' nk_le],
  rw mul_comm at h1 h2,
  exact_mod_cast h2.trans h1.symm,
  exact_mod_cast ne_of_gt non_triv
end

/- Proof of the main theorem -/

theorem lamp_thm : lamp_prop
:= begin
  show ∀ n k : ℕ, 0 < n → n ≤ k →
    (N_num n k : ℚ) / (M_num n k) = 2^(k-n),
  intros n k n_pos nk_le,
  apply lamp_arith,
    show N_num n k * 2^n = D_num n k, by apply N_num_by_D_num,
    show M_num n k * 2^k = D_num n k, by apply M_num_by_D_num,
    show M_num n k > 0, from M_num_nontriv n_pos nk_le,
    show n ≤ k, from nk_le,
end

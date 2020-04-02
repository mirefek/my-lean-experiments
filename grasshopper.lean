import tactic
import data.finset

-----------------------------------------------------------------
---------------------     helpers   -----------------------------

def subtract_emb (c:ℤ) : ℤ ↪ ℤ := ⟨λx:ℤ, x-c, begin
  intros,
  unfold function.injective,
  show ∀ x y : ℤ, x-c = y-c → x = y, by omega,
end⟩

lemma lt_of_le_ne (a b : ℤ) (h1 : a ≤ b) (h2 : a ≠ b) : (a < b)
:=
begin
  cases lt_trichotomy a b,
    show a < b, by assumption,
  cases h,
    by contradiction,
    omega,
end

---------------------     helpers   -----------------------------
-----------------------------------------------------------------
------------------   finset operations   ------------------------

lemma finset_rest {s : finset ℤ} {x : ℤ} (x_in_s : x ∈ s) :
  ∃ r : finset ℤ, s.val = x::r.val
:=
begin
  cases (@multiset.exists_cons_of_mem ℤ s.val x x_in_s) with r_ms r_h,
  have s_nodup : multiset.nodup (x::r_ms), begin
    rw ←r_h, exact s.nodup
  end,
  have : r_ms.nodup, exact (multiset.nodup_cons.elim_left s_nodup).2,
  let r : finset ℤ := ⟨r_ms, this⟩,
  show ∃ (r : finset ℤ), s.val = x :: r.val, from ⟨r, r_h⟩
end

lemma finset_cons_subset {s : finset ℤ} {s2 : finset ℤ} {x:ℤ}
  (h : s.val = x::s2.val) : s2 ⊂ s
:=
begin
  apply finset.val_lt_iff.elim_left,
  rw h,
  show s2.val < x :: s2.val, from multiset.lt_cons_self s2.val x,
end

theorem sum_filter_split {p : ℤ → Prop} [decidable_pred p] (s : finset ℤ) :
  s.card = (s.filter p).card + (s.filter (λa, ¬ p a)).card
:=
begin
  let s1 := s.filter p,
  let s2 := s.filter (λa, ¬ p a),
  have inter_empty : s1 ∩ s2 = ∅,
    by exact finset.filter_inter_filter_neg_eq s,
  have union_full : s1 ∪ s2 = s,
    by exact finset.filter_union_filter_neg_eq s,
  have : (s1 ∪ s2).card + (s1 ∩ s2).card = s1.card + s2.card,
    by apply finset.card_union_add_card_inter,
  rw [inter_empty, finset.card_empty, add_zero] at this,
  show s.card = s1.card + s2.card,
  rw ←union_full,
  show (s1 ∪ s2).card = s1.card + s2.card, from this
end

------------------   finset operations   ------------------------
-----------------------------------------------------------------
-----------------    handling prefixes   ------------------------

lemma cons_prefix (x : ℤ) (a : list ℤ) : [x] <+: x::a
:=
begin
  have : [x] = list.take 1 (x::a), by simp,
  rw this,
  show list.take 1 (x :: a) <+: x :: a, by apply list.take_prefix,
end

lemma prefix_one_eq {x : ℤ} {y : ℤ} {l : list ℤ}
  (h1 : [x] <+: l) (h2 : [y] <+: l)
  : x = y
:=
begin
  have xy : [x] <+: [y] := list.prefix_of_prefix_length_le h1 h2 (by simp),
  have : [x] = [y], from list.eq_of_prefix_of_length_eq xy (by simp),
  simp at this,
  show x = y, from this,
end

lemma prefix_eq_head {x y : ℤ} {a b : list ℤ}
  (h : list.cons x a ∈ (list.cons y b).inits)
  : x = y
:=
begin
  have pref : x::a <+: y::b, from (list.mem_inits (x::a) (y::b)).1 h,
  have xxa : [x] <+: x::a, by apply cons_prefix,
  have yyb : [y] <+: y::b, by apply cons_prefix,
  have xyb : [x] <+: y::b, from list.is_prefix.trans xxa pref,
  show x = y, from prefix_one_eq xyb yyb,
end

lemma prefix_tail_prefix {x y : ℤ} {a b : list ℤ}
  (h : list.cons x a ∈ (list.cons y b).inits)
  : a ∈ b.inits
:=
begin
  have : x = y, from prefix_eq_head h,
  rw ←this at h,
  have : x::a <+: x::b, from (list.mem_inits (x::a) (x::b)).1 h,
  have : a <+: b, from (list.prefix_cons_inj x).1 this,
  show a ∈ b.inits, from (list.mem_inits a b).2 this,
end

-----------------    handling prefixes   ------------------------
-----------------------------------------------------------------
-------------    sum of positive integers   ---------------------

lemma l_nonneg_sum {l : list ℤ} (h1 : ∀ x ∈ l, (0:ℤ) < x)
  : l.sum ≥ 0
:=
begin
  induction l,
    show [].sum ≥ (0:ℤ), by simp,
    show list.sum (l_hd :: l_tl) ≥ (0:ℤ),
    have : list.sum (l_hd :: l_tl) = l_hd + l_tl.sum, by simp,
    rw this,
    show l_hd + l_tl.sum ≥ 0,
    have : l_hd ≥ 0, begin
      apply le_of_lt,
      apply h1,
      show l_hd ∈ list.cons l_hd l_tl, by apply list.mem_cons_self,
    end,
    have : l_tl.sum ≥ 0, begin
      apply l_ih,
      assume (x:ℤ) (tl_in : x ∈ l_tl),
      show 0 < x,
      apply h1,
      apply list.mem_cons_of_mem,
      show x ∈ l_tl, by assumption,
    end,
    omega,
end

lemma pref_nonneg_sum {jumps : finset ℤ} {jumps_l : list ℤ} {jumps_pref : list ℤ}
  (h1 : ∀ jump ∈ jumps, (0:ℤ) < jump) (h2 : jumps.val = jumps_l)
  (h3 : jumps_pref ∈ jumps_l.inits)
  : jumps_pref.sum ≥ 0
:=
begin
  apply l_nonneg_sum,
  assume (jump:ℤ) (h : jump ∈ jumps_pref),
  apply h1,
  show jump ∈ jumps,
  apply finset.mem_def.2,
  rw h2,
  show jump ∈ jumps_l,
  have : jumps_pref ⊆ jumps_l, begin
    apply list.subset_of_sublist,
    apply list.sublist_of_prefix,
    apply (list.mem_inits jumps_pref jumps_l).1,
    show jumps_pref ∈ jumps_l.inits, from h3,
  end,
  apply (list.subset_def.1 this),
  show jump ∈ jumps_pref, from h,
end

-------------    sum of positive integers   ---------------------
-----------------------------------------------------------------
-----------------    the main theorem   -------------------------

theorem grasshopper :
  forall n : ℕ,
  forall jumps : finset ℤ,
  (forall jump ∈ jumps, (0:ℤ) < jump) →
  (jumps.card = n) →
  let size := jumps.1.sum in
  forall mines : finset ℤ,
  (mines.card < n) →
  (forall mine ∈ mines, (0:ℤ) < mine ∧ mine < size)
  →
  exists jumps_l : list ℤ,
  jumps.1 = jumps_l ∧
  forall jumps_pref ∈ jumps_l.inits,
  list.sum jumps_pref ∉ mines
:=
begin
  assume n,
  induction n with n n_ih, -- zero case is trivial
    intros,
    have : mines.card < 0, by assumption,
    have : ¬mines.card < 0, by apply nat.not_lt_zero,
    contradiction,
  intros, -- inductive case

  -- Take the maximal jump
  have : jumps.nonempty, by simp [a_1, finset.card_pos.elim_left],
  cases finset.max_of_nonempty this with maxjump maxjump_ex,
  have maxjump_in : maxjump ∈ jumps, by exact finset.mem_of_max maxjump_ex,
  cases finset_rest maxjump_in with jumps_res jumps_res_ex,

  -- Remove the maximal jump, partial plugging into IH
  have : jumps_res ⊆ jumps, from and.elim_left (finset_cons_subset jumps_res_ex),
  have jumps_res_pos : ∀ jump ∈ jumps_res, (0:ℤ) < jump, begin
    intro jump,
    assume h : jump ∈ jumps_res,
    have : jump ∈ jumps, from finset.mem_of_subset this h,
    show 0 < jump, from a jump this,
  end,
  have n_ih := n_ih jumps_res jumps_res_pos begin
    show jumps_res.card = n,
    apply nat.succ_inj,
    rw ←a_1,
    show jumps_res.card.succ = jumps.card,
    have : (maxjump :: jumps_res.val).card = jumps_res.val.card + 1,
      by apply multiset.card_cons,
    rw ←jumps_res_ex at this,
    exact eq.symm this,
  end,

  -- Calculate the remaining size
  let size_res := jumps_res.1.sum,
  have size_res_eq : size_res = size - maxjump, begin
    show multiset.sum jumps_res.val = multiset.sum jumps.val - maxjump,
    rw jumps_res_ex,
    rw multiset.sum_cons,
    ring,
  end,

  -- Shift the mines by maxjump to the left
  let mines_smaller := finset.filter (λ(x:ℤ), x < maxjump) mines,
  let mines_bigger := finset.filter (λ(x:ℤ), ¬x < maxjump) mines,
  have parts_size : mines.card = mines_smaller.card + mines_bigger.card,
    by apply sum_filter_split,
  let mines_sub := finset.map (subtract_emb maxjump) mines_bigger,
  have mines_sub_rev : ∀ mine ∈ mines_sub, mine + maxjump ∈ mines ∧ 0 ≤ mine, begin
    intros,
    cases finset.mem_map.elim_left H with mine_ori mine_ori_prop,
    cases mine_ori_prop with mine_ori_in_bigger mine_ori_def,
    show mine + maxjump ∈ mines ∧ 0 ≤ mine, rw [←mine_ori_def],
    show mine_ori - maxjump + maxjump ∈ mines ∧ 0 ≤ mine_ori - maxjump,
    apply and.intro, begin
      simp,
      show mine_ori ∈ mines,
      apply finset.mem_of_subset,
        show mine_ori ∈ mines_bigger, by assumption,
        show mines_bigger ⊆ mines, by simp,
    end, begin
      show 0 ≤ mine_ori - maxjump,
      have : ¬(mine_ori < maxjump), from (finset.mem_filter.1 mine_ori_in_bigger).2,
      omega,
    end
  end,
  have mines_sub_small : ∀ mine ∈ mines_sub, mine < size_res, begin
    intros,
    have : mine + maxjump ∈ mines, from (mines_sub_rev mine H).1,
    have : mine + maxjump < size, from (a_3 (mine + maxjump) this).2,
    show mine < size_res, by omega,
  end,

  ------------------------------------------
  ---------- case analysis

  cases (classical.em (maxjump ∈ mines))
    with mine_on_maxjump mine_not_on_maxjump,
  -- case A: first jump to mine
  begin
    sorry,
  end,
  -- cases C and B
    have mines_sub_positive : ∀ mine ∈ mines_sub, (0:ℤ) < mine, begin
      assume (mine : ℤ) (mine_in : mine ∈ mines_sub),
      apply lt_of_le_ne,
        show 0 ≤ mine, from (mines_sub_rev mine mine_in).2,
        show 0 ≠ mine, begin
          assume mine_zero : 0 = mine,
          have : mine + maxjump ∈ mines, from (mines_sub_rev mine mine_in).1,
          simp [←mine_zero] at this,
          contradiction,
        end
    end,
    cases (classical.em mines_smaller.nonempty)
      with mines_smaller_nonempty mines_smaller_empty,
  -- case C: we jump over a mine with the first jump
  begin

    have : mines_sub.card < n, begin
      have : mines_sub.card = mines_bigger.card,
        by apply finset.card_map,
      rw this,
      have : finset.card mines_smaller > 0,
        by exact finset.card_pos.2 mines_smaller_nonempty,
      have smaller_ge : 1 ≤ finset.card mines_smaller, exact nat.succ_le_iff.2 this,
      rw parts_size at a_2,
      have : finset.card mines_smaller + finset.card mines_bigger ≤ n,
        from nat.lt_succ_iff.1 a_2,
      show mines_bigger.card < n, from calc
        mines_bigger.card < mines_bigger.card + 1 : by apply nat.lt_succ_self
          ...             ≤ mines_bigger.card + mines_smaller.card :
                                     by apply add_le_add_left smaller_ge
          ...             = mines_smaller.card + mines_bigger.card : by apply nat.add_comm
          ...             ≤ n : this
    end,

    -- plug mines_sub to the IH, and get jumps_l_ind, jumps_l_ind_prop
    cases n_ih mines_sub this begin
      show ∀ (mine : ℤ), mine ∈ mines_sub → 0 < mine ∧ mine < size_res,
      assume (mine : ℤ) (mine_in : mine ∈ mines_sub),
      apply and.intro,
      show 0 < mine, from mines_sub_positive mine mine_in,
      show mine < size_res, from mines_sub_small mine mine_in
    end with jumps_l_ind jumps_l_ind_prop,

    let jumps_l : list ℤ := maxjump::jumps_l_ind,
    apply exists.intro jumps_l,
    apply and.intro,
      show jumps.val = ↑(maxjump :: jumps_l_ind),
        by simp [jumps_res_ex, jumps_l_ind_prop.1],
      show ∀ jumps_pref ∈ jumps_l.inits, list.sum jumps_pref ∉ mines,
        intros,
        cases jumps_pref,
          -- jumps_pref empty
          assume : (0:ℤ) ∈ mines,
          show false, from lt_irrefl (0:ℤ) (a_3 (0:ℤ) this).1,
          -- jumps_pref nonempty
          have : jumps_pref_hd = maxjump, from prefix_eq_head H,
          rw this,
          have : list.sum (maxjump :: jumps_pref_tl) = maxjump + jumps_pref_tl.sum,
            by simp,
          rw this,
          assume in_mines : maxjump + jumps_pref_tl.sum ∈ mines,
          have pref_tl_in_inits : jumps_pref_tl ∈ jumps_l_ind.inits,
            from prefix_tail_prefix H,
          have not_in_mines_sub: jumps_pref_tl.sum ∉ mines_sub,
            from jumps_l_ind_prop.2 jumps_pref_tl pref_tl_in_inits,
          have : ¬(maxjump + jumps_pref_tl.sum) < maxjump, begin
            have jumps_tl_sum_ge : jumps_pref_tl.sum ≥ (0:ℤ),
              from pref_nonneg_sum jumps_res_pos jumps_l_ind_prop.1 pref_tl_in_inits,
            have : maxjump + (0:ℤ) ≤ maxjump + jumps_pref_tl.sum,
              from add_le_add_left jumps_tl_sum_ge maxjump,
            omega,
          end,
          have in_mines_bigger : maxjump + jumps_pref_tl.sum ∈ mines_bigger,
            by simp [in_mines, this],
          have : (subtract_emb maxjump) (maxjump + jumps_pref_tl.sum) = jumps_pref_tl.sum,
            by apply add_sub_cancel',
          have : jumps_pref_tl.sum ∈ mines_sub, begin
            apply finset.mem_map.2,
            apply exists.intro (maxjump + jumps_pref_tl.sum),
            apply exists.intro in_mines_bigger,
            exact this,
          end,
          contradiction,
  end,
  -- case B: all mines are far away
  begin
    sorry,
  end
end

-----------------    the main theorem   -------------------------
-----------------------------------------------------------------

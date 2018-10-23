/-
The task:
1) Define clone (see Wikipedia https://en.wikipedia.org/wiki/Clone_(algebra) )
2) Proof that in every clone,
  if there is a ternary operation p satisfying p(y,x,x) = p(y,x,y) = p(x,x,y) = y
  then there is a ternary operation m satisfying m(y,x,x) = m(x,y,x) = m(x,x,y) = x
  (hint: m(a,b,c) = p(a,p(a,b,c),c) )

TODO:
1) expand forall conjunction -> conjunction forall by a tactic?
2) tactic for cases of fin
3) use several rewrite rules as long as possible
4) general version of compose3_lemma ()
-/

-- handy way of writing arrays
def list.a {α : Type} (l : list α) : array (l.length) α :=
{ data := λ i, l.nth_le i.val i.is_lt}
#check [2,3,4,5].a
#reduce [2,3,4,5].a

-- ability to map array from one type to another
def array.my_map {α β : Type} {n : ℕ} (f : α → β) (a : array n α) : array n β :=
{data := λ i : fin n, f (a.data i)}

-- lemma for case-analysis on natural numbers
theorem not_lt_cases {n : ℕ} {i_val : ℕ} (h : ¬i_val < n) :
i_val = n ∨ ¬(i_val < nat.succ(n)) :=
begin
have: i_val = n ∨ n < i_val, from nat.eq_or_lt_of_not_lt h,
cases this, left, assumption,
right, have: ¬ i_val ≤ n, from (nat.lt_iff_le_not_le.elim_left this).right,
intro a, revert this, apply non_contradictory_intro,
show i_val ≤ n, from nat.le_of_lt_succ a
end

-- operations, composition, projections
def operation (ar : ℕ) (α : Type) := (array ar α) → α
def compose {α : Type} {n m : ℕ} (f : operation n α)
  (g_tup : array n (operation m α)) :
operation m α :=
  assume input : array m α,
  f (g_tup.my_map (λ g, g input))

constants f : operation 3 ℕ
theorem compose3_lemma {α : Type} {m : ℕ} {f : operation 3 α} {g1 g2 g3 : operation m α}
: compose f [g1, g2, g3].a = λ input, f [g1 input, g2 input, g3 input].a :=
begin
apply funext,
intros,
apply congr_arg f,
apply array.ext,
intros,
cases i,
  by_cases i_val = 0, subst i_val, refl,
  by_cases i_val = 1, subst i_val, refl,
  by_cases i_val = 2, subst i_val, refl,
  have ineq := nat.not_lt_zero i_val,
  iterate 3 {have ineq := not_lt_cases ineq, cases ineq with neq ineq, contradiction},
  contradiction,
end

def projection (α : Type) (n : ℕ) (i : fin n) :
operation n α := λ input, input.read i

-- clone

def operation_set (α : Type) : Type := Π n : ℕ, set (operation n α)

def is_clone {α : Type} (ops : operation_set α) : Prop :=
(∀ n : ℕ, ∀ i : fin n, projection α n i ∈ ops n) ∧
(∀ n m : ℕ,
  ∀ f, f ∈ ops n →
  ∀ g_tup : array n (operation m α),
  (∀ i, g_tup.read i ∈ ops m) →
    compose f g_tup ∈ ops m)

-- testing proposition
theorem clone_prop {α : Type} (ops : operation_set α) (hclone: is_clone ops) :
(∃ (p : operation 3 α), p ∈ ops 3 ∧ ∀ x y,
   p [y,x,x].a = y ∧
   p [y,x,y].a = y ∧
   p [x,x,y].a = y
) → (∃ (m : operation 3 α), m ∈ ops 3 ∧ ∀ x y,
   m [y,x,x].a = x ∧
   m [x,y,x].a = x ∧
   m [x,x,y].a = x
) :=
let π₁ := projection α 3 (⟨0, by comp_val⟩ : fin 3) in
let π₃ := projection α 3 (⟨2, by comp_val⟩ : fin 3) in
begin
intro h,
cases h with p hp,
cases hclone with has_proj has_compositions,
cases hp,
existsi compose p [π₁, p, π₃].a,
constructor,
  -- m is in the clone
  have has_comp_concrete := has_compositions 3 3 p hp_left [π₁, p, π₃].a,
  apply has_comp_concrete,
  intro i, cases i,
  by_cases i_val = 0, subst i_val, show π₁ ∈ ops 3, from has_proj 3 0,
  by_cases i_val = 1, subst i_val, show p ∈ ops 3, by assumption,
  by_cases i_val = 2, subst i_val, show π₃ ∈ ops 3, from has_proj 3 2,
  have ineq := nat.not_lt_zero i_val,
  iterate 3 {have ineq := not_lt_cases ineq, cases ineq with neq ineq, contradiction},
  contradiction,

  -- m satisfies the identities

  -- state the necessary identities
  have p1: ∀ (x y : α), p [y, x, x].a = y, intros, apply (hp_right x y).left,
  have p2: ∀ (x y : α), p [y, x, y].a = y, intros, apply (hp_right x y).right.left,
  have p3: ∀ (x y : α), p [x, x, y].a = y, intros, apply (hp_right x y).right.right,
  have pi1: ∀ (a b c : α), π₁ [a, b, c].a = a, intros, refl,
  have pi3: ∀ (a b c : α), π₃ [a, b, c].a = c, intros, refl,
  intros,
  simp [compose3_lemma],
  -- and apply them
  iterate 10 { /- a bit hacky, how to just rewrite
                  all the (nested) occurences of (p1 p2 p3 pi1 pi3)? -/
    try {rw p1}, try {rw p2}, try {rw p3}, try {rw pi1}, try {rw pi3},
  },
  simp,
end

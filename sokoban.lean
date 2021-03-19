import tactic
import data.list.func

universe u

def list2d (α : Type u) := list (list α)

namespace list2d

open list.func

variables {α : Type} {β : Type}
variables [inhabited α] [inhabited β]

@[simp] def get2d (xy : ℕ × ℕ) (l : list2d α) : α
  := let (x,y) := xy in get x (get y l)
@[simp] def set2d (a : α) (l : list2d α) (xy : ℕ × ℕ) : list2d α
  := let (x,y) := xy in set (set a (get y l) x) l y
@[simp] def dfzip2d (l1 : list2d α) (l2 : list2d β) : list2d (α × β)
  := (pointwise (pointwise prod.mk) l1 l2)
@[simp] def add_to_line1 (a : α) : list2d α -> list2d α
| [] := [[a]]
| (h::t) := (a::h)::t

@[simp] def transpose : list2d α → list2d α := (list.foldr (pointwise list.cons)) []

instance [has_repr α] : has_repr (list2d α) := ⟨λ l, list.repr (l : list (list α))⟩

#eval transpose [[1, 2], [3, 4, 5], [6]]

end list2d

inductive direction : Type
| up
| down
| left
| right

namespace direction

def opposite : direction -> direction
| up := down
| down := up
| left := right
| right := left

def shift : direction -> (ℕ × ℕ) -> option (ℕ × ℕ)
| up (_, 0)     := none
| up (x, y+1)   := some (x, y)
| down (x, y)   := some (x, y+1)
| left (0, _)   := none
| left (x+1, y) := some (x, y)
| right (x, y)   := some (x+1, y)

end direction

structure sokoban :=
(available : list2d bool)
(boxes : list2d bool)
(storages : list2d bool)
(storekeeper : ℕ × ℕ)

namespace sokoban
open list2d

instance : inhabited sokoban
:= ⟨{ available := [[tt]], boxes := [], storages := [], storekeeper := (0,0) }⟩

@[simp] def move (d : direction) (s : sokoban) : sokoban :=
  match (d.shift s.storekeeper) with none := s
  | some sk2 :=
  if get2d sk2 s.available = false then s else
  if get2d sk2 s.boxes = false then
    { storekeeper := sk2, ..s}
  else
    match (d.shift sk2) with none := s
    | some box2 :=
    if (get2d box2 s.available = false)
      ∨ (get2d box2 s.boxes = true) then s else
    {
      boxes := (s.boxes.set2d ff sk2).set2d tt box2,
      storekeeper := sk2, ..s
    }
    end
  end

@[simp] def move_up := move direction.up
@[simp] def move_down := move direction.down
@[simp] def move_left := move direction.left
@[simp] def move_right := move direction.right

@[simp] def add_newline (s : sokoban) : sokoban := {
  available := []::s.available,
  boxes := []::s.boxes,
  storages := []::s.storages,
  storekeeper := match s.storekeeper with (x,y) := (x,y+1) end
}
@[simp] def add_newsquare (av box stor sk : bool) (s : sokoban) : sokoban := {
  available := add_to_line1 av s.available,
  boxes := add_to_line1 box s.boxes,
  storages := add_to_line1 stor s.storages,
  storekeeper := if sk then (0, 0) else match s.storekeeper with
    | (x,0) := (x+1,0)
    | xy := xy
  end
}

@[simp] def from_string_aux : list char → option (sokoban × bool)
| [] := some (sokoban.mk [] [] [] (0,0), ff)
| (c::str) := match (from_string_aux str), c with
  | none, _ := none
  | (some (s, sk_set)), '\n' := some (add_newline s, sk_set)
  | (some (s, sk_set)), ' ' := some (add_newsquare tt ff ff ff s, sk_set)
  | (some (s, sk_set)), '#' := some (add_newsquare ff ff ff ff s, sk_set)
  | (some (s, sk_set)), '.' := some (add_newsquare tt ff tt ff s, sk_set)
  | (some (s, sk_set)), '$' := some (add_newsquare tt tt ff ff s, sk_set)
  | (some (s, sk_set)), '*' := some (add_newsquare tt tt tt ff s, sk_set)
  | (some (s, ff)), '@' := some (add_newsquare tt ff ff tt s, tt)
  | (some (s, ff)), '+' := some (add_newsquare tt ff tt tt s, tt)
  | (some _), _ := none
  end

@[simp] def from_string (str : string) : sokoban :=
  match (from_string_aux str.to_list) with
  | none := default sokoban
  | some (_, ff) := default sokoban
  | some (level, tt) := level
  end

@[simp] def square_to_char : bool → bool → bool → bool → char
| tt ff ff ff := ' '
| ff ff ff ff := '#'
| tt ff tt ff := '.'
| tt tt ff ff := '$'
| tt tt tt ff := '*'
| tt ff ff tt := '@'
| tt ff tt tt := '+'
| _ _ _ _ := '?'

@[simp] def to_string_aux1 (str : list char) : list (bool × bool × bool × bool) → list char
| [] := str
| ((av,box,stor,sk)::t) := (square_to_char av box stor sk)::(to_string_aux1 t)

@[simp] def to_string_aux2 : list2d (bool × bool × bool × bool) → list char
| [] := []
| (h::t) := to_string_aux1 ('\n'::(to_string_aux2 t)) h

instance : has_to_string sokoban := ⟨λ s,
  list.as_string (to_string_aux2
  (dfzip2d s.available (dfzip2d s.boxes (dfzip2d s.storages (set2d true [] s.storekeeper)))))
⟩

instance : has_repr sokoban
:= ⟨λ s, (string.append (string.append "sokoban.from_string \"" (to_string s)) "\"")⟩

inductive solvable : sokoban -> Prop
| solved (s : sokoban) (H : s.boxes = s.storages) : solvable s
| move (d : direction) (s : sokoban) (H : solvable (s.move d)) : solvable s

@[simp] def solvable.move_up := solvable.move direction.up
@[simp] def solvable.move_down := solvable.move direction.down
@[simp] def solvable.move_left := solvable.move direction.left
@[simp] def solvable.move_right := solvable.move direction.right

end sokoban

def soko_level := sokoban.from_string "
#######
#. . .#
# $$$ #
#.$@$.#
# $$$ #
#. . .#
#######
"
/-
def soko_level_decoded : sokoban :=
{available := [list.nil, [ff, ff, ff, ff, ff, ff, ff], [ff, tt, tt, tt, tt, tt, ff], [ff, tt, tt, tt, tt, tt, ff], [ff, tt, tt, tt, tt, tt, ff], [ff, tt, tt, tt, tt, tt, ff], [ff, tt, tt, tt, tt, tt, ff], [ff, ff, ff, ff, ff, ff, ff]],
 boxes := [list.nil, [ff, ff, ff, ff, ff, ff, ff], [ff, ff, ff, ff, ff, ff, ff], [ff, ff, tt, tt, tt, ff, ff], [ff, ff, tt, ff, tt, ff, ff], [ff, ff, tt, tt, tt, ff, ff], [ff, ff, ff, ff, ff, ff, ff], [ff, ff, ff, ff, ff, ff, ff]],
 storages := [list.nil, [ff, ff, ff, ff, ff, ff, ff], [ff, tt, ff, tt, ff, tt, ff], [ff, ff, ff, ff, ff, ff, ff], [ff, tt, ff, ff, ff, tt, ff], [ff, ff, ff, ff, ff, ff, ff], [ff, tt, ff, tt, ff, tt, ff], [ff, ff, ff, ff, ff, ff, ff]],
 storekeeper := (3, 4)}
-/

example : sokoban.solvable soko_level :=
begin
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_right,
/-
#######
#. * .#
#$   $#
#.$ $.#
#$  @$#
#. * .#
#######
-/
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_right,
/-
#######
#. * *#
#   $ #
#*  @.#
#  $ $#
#* * .#
#######
-/
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_right,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_left,
  apply sokoban.solvable.move_down,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.move_up,
  apply sokoban.solvable.solved,
  reflexivity
end

#eval soko_level.move_up.move_left.move_right.move_right.move_left.move_down.move_down.move_left.move_right.move_right.move_up.move_right.move_up.move_down.move_left.move_left.move_up.move_left.move_down.move_left.move_down.move_right.move_up.move_up.move_up.move_left.move_down.move_right.move_down.move_right.move_right.move_right.move_up.move_left.move_down.move_down.move_down.move_right.move_up.move_left.move_up.move_up.move_up.move_left.move_left.move_down.move_down.move_down.move_down.move_right.move_right.move_up.move_up.move_left.move_down.move_up.move_up

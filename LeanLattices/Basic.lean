import Mathlib

-- ==============================
-- some basic PartialOrder proofs
-- ==============================

noncomputable example [PartialOrder α] (a b : α) (h : a < b) : a ≤ b := by
  rw [@le_iff_eq_or_lt] -- ⊢ a = b ∨ a < b
  right -- ⊢ a < b
  exact h

noncomputable example [PartialOrder α] (a b : α) (h : a = b) : a ≤ b := by
  rw [@le_iff_eq_or_lt] -- ⊢ a = b ∨ a < b
  left -- ⊢ a = b
  exact h

noncomputable example [PartialOrder α] (a b : α) (h : a = b ∨ a < b) : a ≤ b := by
  rw [@le_iff_eq_or_lt] -- ⊢ a = b ∨ a < b
  exact h

-- definition of an upper bound, a term of α relative to a set of α (as a proposition)
def y_is_upper_bound' [PartialOrder α] (X : Set α) (y : α) := ∀ x ∈ X, x ≤ y
#check y_is_upper_bound'

-- ===========================
-- similar for CompleteLattice
-- ===========================
theorem a_eq_b_or_a_lt_b_means_a_le_b [CompleteLattice α] (a b : α) (h : a = b ∨ a < b)
  : a ≤ b := by
  rw [@le_iff_eq_or_lt] -- ⊢ a = b ∨ a < b
  exact h

def is_upper_bound [CompleteLattice α] [Lattice α] (X : Set α) (y : α) := ∀ x ∈ X, x ≤ y

-- can use the powerful order tactic
noncomputable example [CompleteLattice α] (X : Set α) : is_upper_bound X ⊤ := by
  intro x
  order

noncomputable example [CompleteLattice α] (X : Set α) : is_upper_bound X (sSup X) := by
  intro x
  exact le_sSup

-- ====================
-- with a concrete type
inductive Sign where
  | Top
  | Neg
  | Zero
  | Pos
  | Bot
  deriving BEq

instance : LE Sign where
  le a b := match a, b with
  | .Top, .Top | .Neg, .Neg
  | .Zero, .Zero | .Pos, .Pos
  | .Bot, .Bot => true
  --
  | .Top, _ => false
  | _, .Top => true
  | .Bot, _ => true
  | _, .Bot => false
  | _, _ => false

instance : PartialOrder Sign where
  le_refl a : a ≤ a := by
    -- rfl can tell every a is ≤ a case-wise, but you need to introduce the cases.
    -- i.e. `by rfl` is insufficient
    cases a with
    | _ => rfl
  le_trans (a b c : Sign) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
    match a, b, c with
    | Sign.Bot, _, Sign.Top
    | Sign.Bot, _, Sign.Neg
    | Sign.Bot, _, Sign.Zero
    | Sign.Bot, _, Sign.Pos
    | Sign.Bot, _, Sign.Bot
    | Sign.Pos, _, Sign.Top
    | Sign.Zero, _, Sign.Top
    | Sign.Neg, _, Sign.Top
    | Sign.Top, _, Sign.Top => exact le_of_eq_of_le rfl rfl -- does this make a = b always?
    -- I don't know what's up with these cases that have ⊥ as c
    | Sign.Top, Sign.Pos, Sign.Bot
    | Sign.Top, Sign.Zero, Sign.Bot
    | Sign.Top, Sign.Neg, Sign.Bot
    | Sign.Pos, Sign.Neg, Sign.Bot
    | Sign.Pos, Sign.Zero, Sign.Bot
    | Sign.Zero, Sign.Neg, Sign.Bot
    | Sign.Zero, Sign.Pos, Sign.Bot
    | Sign.Neg, Sign.Pos, Sign.Bot => exact le_of_eq_of_le rfl h1
    | Sign.Pos, Sign.Pos, Sign.Pos
    | Sign.Neg, Sign.Neg, Sign.Neg
    | Sign.Zero, Sign.Zero, Sign.Zero => exact rfl
  le_antisymm (a b : Sign) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
    match a, b with
    -- match removes obviously contradictory states (!!! this is so cool)
    | Sign.Top, Sign.Top | Sign.Neg, Sign.Neg
    | Sign.Zero, Sign.Zero | Sign.Pos, Sign.Pos | Sign.Bot, Sign.Bot => rfl

noncomputable example : Set Sign := singleton Sign.Top

instance : CompleteLattice Sign where
  top := .Top
  bot := .Bot
  le_top a : a ≤ .Top := by
    cases a with
    | _ => exact le_of_eq_of_le rfl rfl
  bot_le a : .Bot ≤ a := by
    cases a with
    | _ => exact le_of_eq_of_le rfl rfl
  sup a b :=
    match a, b with
    | .Top, .Top | .Neg, .Neg | .Zero, .Zero | .Pos, .Pos | .Bot, .Bot => a
    | .Top, _ | _, .Top => .Top
    | .Bot, s | s, .Bot => s
    | _, _ => .Top
  inf a b :=
    match a, b with
    | .Top, .Top | .Neg, .Neg | .Zero, .Zero | .Pos, .Pos | .Bot, .Bot => a
    | .Top, s | s, .Top => s
    | .Bot, _ | _, .Bot => .Bot
    | _, _ => .Bot
  le_inf (a b c) (h1 : a ≤ b) (h2 : a ≤ c) := by grind =>
    cases #df5d
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · sorry
  sup_le (a b c) (h1 : a ≤ c) (h2 : b ≤ c) := by grind =>
    cases #711f
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · instantiate only
    · sorry
  -- sSup (s : Set Sign) : Sign :=
  --   match s with
  --   | Empty => .Bot
  --   | singleton a => a

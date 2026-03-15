import Mathlib

-- file makes sporadic use of `Classical` as decidability makes things much easier to reason about

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
  deriving DecidableEq

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

-- ≤ is decidable
open Classical in
#check if Sign.Top ≤ Sign.Top then 1 else 2

open Sign in
theorem Sign.le_refl (a : Sign) : a ≤ a := by
  cases a with
  | _ => rfl

instance : PartialOrder Sign where
  le_refl := Sign.le_refl
  le_trans (a b c : Sign) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
    if a = c then {
      (expose_names; rw [← h])
      exact Sign.le_refl a
    } else if a = b then {
      (expose_names; rw [h_1])
      exact h2
    } else if b = c then {
      (expose_names; rw [← h_2])
      exact h1
    } else {
      match a, b, c with
      |  .Bot, _, .Top | .Bot, _, .Neg
      | .Bot, _, .Zero | .Bot, _, .Pos => exact le_of_eq_of_le rfl rfl
    }
  le_antisymm (a b : Sign) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
    match a, b with
    -- match removes obviously contradictory states (!!! this is so cool)
    | Sign.Top, Sign.Top | Sign.Neg, Sign.Neg
    | Sign.Zero, Sign.Zero | Sign.Pos, Sign.Pos | Sign.Bot, Sign.Bot => rfl

noncomputable example : Set Sign := singleton Sign.Top

open Sign in
def sup [DecidableLE Sign] (a b : Sign) : Sign := if a ≤ b then b else a

open Sign in
def letop [DecidableLE Sign] (a : Sign) : a ≤ .Top := by
  cases a with
  | _ => exact le_of_eq_of_le rfl rfl
open Sign in
def botle (a : Sign) : .Bot ≤ a := by
  cases a with
  | _ => exact le_of_eq_of_le rfl rfl

open Sign in
lemma le_sup_l [DecidableLE Sign] a b : a ≤ sup a b := by
  set c := sup a b
  if a = c then {
    (expose_names; exact le_of_eq h)
  } else {
    sorry
    -- TODO: wanted to turn this into a match but had a weird issue
    -- with obviously contradictory orderings; after several hours of debugging,
    -- decided to go to bed and get back at it later.
  }

theorem le_sup_r [DecidableLE Sign] a b : b ≤ sup a b := sorry

instance [DecidableLE Sign] : CompleteLattice Sign where
  top := .Top
  bot := .Bot
  le_top := letop
  bot_le := botle
  sup := sup
  le_sup_left := le_sup_l
  le_sup_right a b := by sorry
  inf a b := if a ≤ b then a else b
  inf_le_left a b := by sorry
  inf_le_right a b := by sorry
  -- ======================================
  sSup (s : Set Sign) : Sign := sorry
  sInf (s : Set Sign) : Sign := sorry
  le_sSup (s : Set Sign) := sorry
  sSup_le (s : Set Sign) := sorry
  sInf_le (s : Set Sign) := sorry
  le_sInf (s : Set Sign) := sorry
  le_inf (a b c) (h1 : a ≤ b) (h2 : a ≤ c) := by sorry
  sup_le (a b c) (h1 : a ≤ c) (h2 : b ≤ c) := by sorry

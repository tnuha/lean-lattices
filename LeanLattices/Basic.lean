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

noncomputable example [PartialOrder α] (a b : α) (h : ¬ a ≤ b) : (a = b) ∨ (b ≤ a) := by
  -- getting tired but this will help with other proofs
  -- or at least some Prop that looks like this.
  sorry

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

-- ========
-- sup brah
-- ========

-- generic proofs when possible make things extensible
@[reducible]
def sup [PartialOrder α] [DecidableLE α] (a b : α) := if a ≤ b then b else a
lemma larger_is_sup [PartialOrder α] [DecidableLE α] (a b : α) (h : a ≤ b) : b = sup a b
  := by exact Eq.symm (if_pos h)
lemma larger_is_sup' [PartialOrder α] [DecidableLE α] (a b : α) (h : a ≤ b) : b = sup b a
  -- idk what's up with this lemma but this should be as easy to prove as `larger_is_sup`
  := by sorry
noncomputable example [PartialOrder α] [DecidableLE α] (a : α) : a ≤ sup a a := by
  rw [← larger_is_sup]
  rfl
lemma l_le_r_implies_l_le_sup [PartialOrder α] [DecidableLE α] (a b : α) (h : a ≤ b)
: a ≤ sup a b := by
  rw [← larger_is_sup]
  · exact h
  · exact h
lemma supp_symm [PartialOrder α] [DecidableLE α] (a b : α) : sup a b = sup b a := by
  if h : a ≤ b then {
    rw [← larger_is_sup]
    · {
      rw [← larger_is_sup']
      exact h
    }
    · exact h
  } else {
    -- h : ¬ a ≤ b
    -- want to rewrite h as something like (a = b) ∨ (b ≤ a)
    sorry
  }

lemma le_sup_l [PartialOrder α] [DecidableLE α] (a b : α) : a ≤ sup a b := by
  if h : a ≤ b then {
    exact l_le_r_implies_l_le_sup a b h
  } else {
    -- h : ¬ a ≤ b
    -- want to rewrite h as something like (a = b) ∨ (b ≤ a)
    sorry
  }

lemma le_sup_r [PartialOrder α] [DecidableLE α] (a b : α) : b ≤ sup a b := by
  rw [supp_symm]
  exact le_sup_l b a

-- ========
-- inf brah
-- TODO: should look nearly identical to sup proofs, ideally anyway
-- snoop dogg dancing gif
-- ========
@[reducible]
def inf [PartialOrder α] [DecidableLE α] (a b : α) := if a ≤ b then a else b

open Sign in
def letop [DecidableLE Sign] (a : Sign) : a ≤ .Top := by
  cases a with
  | _ => exact le_of_eq_of_le rfl rfl
open Sign in
def botle (a : Sign) : .Bot ≤ a := by
  cases a with
  | _ => exact le_of_eq_of_le rfl rfl

instance [DecidableLE Sign] : CompleteLattice Sign where
  top := .Top
  bot := .Bot
  le_top := letop
  bot_le := botle
  sup := sup
  le_sup_left := le_sup_l
  le_sup_right := le_sup_r
  inf := inf
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

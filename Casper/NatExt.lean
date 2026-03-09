/-
# NatExt - 自然数の拡張

Coq の casper/coq/theories/NatExt.v から翻訳

自然数に関する基本的な拡張と性質を定義します。
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Casper.NatExt

open Nat Finset

/-! ## highest: finite set of nats の最大値 -/

/-- The `highest' value in a finite set of nats -/
def highest (A : Finset ℕ) : ℕ :=
  if h : A.Nonempty then A.max' h else 0

/-- The `highest' is the maximum value (upper bound) -/
theorem highest_ub (A : Finset ℕ) (x : ℕ) (Hx : x ∈ A) : x ≤ highest A := by
  unfold highest
  split_ifs with h
  · exact le_max' A x Hx
  · exact absurd ⟨x, Hx⟩ h

/-! ## 自然数の基本的性質 -/

/-- The successor cannot be smaller -/
theorem ltSnn (n : ℕ) : ¬(n + 1 < n) := by omega

/-- Basic fact about nats: n ≤ 1 implies n = 0 or n = 1 -/
theorem leq_one_means_zero_or_one (n : ℕ) (H_leq : n ≤ 1) : n = 0 ∨ n = 1 := by
  omega

/-- Basic subtraction fact: n - n = 0 -/
theorem sub_eq (n : ℕ) : n - n = 0 := Nat.sub_self n

/-- Conditional associativity of add-sub: (n + m) - p = n + (m - p) when m ≥ p -/
theorem addnDAr (n m p : ℕ) (H : m ≥ p) : (n + m) - p = n + (m - p) := by
  omega

/-! ## one_third と two_third: slashable bound theorem のための抽象化 -/

/--
Two uninterpreted functions to represent quantities used in the slashable bound theorem.
These are not strictly necessary, but they enable using statements and proof arguments
that are closer to the paper.
-/

axiom one_third : ℕ → ℕ
axiom two_third : ℕ → ℕ

/-- Basic axioms assumed to hold for these function symbols -/
axiom thirds_def : ∀ n, n - two_third n = one_third n
axiom leq_two_thirds : ∀ n, two_third n ≤ n

/-- This property follows from leq_two_thirds -/
theorem wt_two_thirds_sum (n m : ℕ) : two_third n + two_third m ≤ n + m := by
  have h1 := leq_two_thirds n
  have h2 := leq_two_thirds m
  omega

end Casper.NatExt

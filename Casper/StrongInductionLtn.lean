/-
# StrongInductionLtn - 強帰納法の原理

Coq の casper/coq/theories/StrongInductionLtn.v から翻訳

自然数上の強帰納法の原理を証明します。
Tej Chajed の研究を参考に実装されています。
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Casper.StrongInductionLtn

open Nat

/-! ## 標準的な強帰納法 -/

/--
標準的な強帰納法の仮説。
標準的な nat の帰納法原理は n = pred m のみを提供し、P 0 が別途必要だが、
強帰納法ではより強い帰納法の仮説を与える。
-/

theorem P0 {P : ℕ → Prop} (IH : ∀ m, (∀ n, n < m → P n) → P m) : P 0 := by
  apply IH
  intro n hn
  exact absurd hn (Nat.not_lt_zero n)

theorem pred_increasing (n m : ℕ) (h : n ≤ m) : n.pred ≤ m.pred := by
  cases n with
  | zero => simp
  | succ n' =>
    cases m with
    | zero => omega
    | succ m' => simp; omega

/-- 補助補題: すべての m ≤ n について P m が成り立つ -/
theorem strong_induction_all {P : ℕ → Prop}
    (IH : ∀ m, (∀ n, n < m → P n) → P m) (n : ℕ) : ∀ m, m ≤ n → P m := by
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := Nat.eq_zero_of_le_zero hm
    rw [this]
    exact P0 IH
  | succ n' ih' =>
    intro m hm
    apply IH
    intro n'' hn''
    apply ih'
    cases Nat.lt_or_eq_of_le hm with
    | inl hlt =>
      -- m < n'.succ の場合
      have : m ≤ n' := Nat.lt_succ_iff.mp hlt
      omega
    | inr heq =>
      -- m = n'.succ の場合
      rw [heq] at hn''
      exact Nat.lt_succ_iff.mp hn''

/-- 強帰納法の原理: すべての n について P n が成り立つ -/
theorem strong_induction_ltn {P : ℕ → Prop}
    (IH : ∀ m, (∀ n, n < m → P n) → P m) : ∀ n, P n := by
  intro n
  exact strong_induction_all IH n n (Nat.le_refl n)

/-! ## 差分に基づく強帰納法 -/

/--
差分に基づく強帰納法の原理。

v1a - k < v1 - k を満たすすべての v1a について P v1a h1a が成り立つならば、
P v1 h1 が成り立つという仮説 IH から、すべての n と t について P n t を導く。
-/
theorem strong_induction_sub {k : ℕ} {T : Type*} {P : ℕ → T → Prop}
    (IH : ∀ (v1 : ℕ) (h1 : T),
      (∀ (v1a : ℕ) (h1a : T), k < v1a → v1a - k < v1 - k → P v1a h1a) → P v1 h1) :
    ∀ n t, P n t := by
  intro n t
  -- strong_induction_ltn を使って証明
  suffices h : ∀ m, (∀ n', n' < m → ∀ t, P n' t) → ∀ t, P m t by
    have := strong_induction_ltn h
    exact this n t
  intro m ih' t
  apply IH
  intro v1a h1a hlt hlt'
  apply ih'
  -- v1a - k < m - k から v1a < m を導く
  have h1 : v1a - k + k < m - k + k := Nat.add_lt_add_right hlt' k
  by_cases hm : k ≤ m
  · rw [Nat.sub_add_cancel hm] at h1
    by_cases hv : k ≤ v1a
    · rw [Nat.sub_add_cancel hv] at h1
      exact h1
    · -- k > v1a の場合、矛盾を導く
      omega
  · -- k > m の場合、矛盾を導く
    omega

end Casper.StrongInductionLtn

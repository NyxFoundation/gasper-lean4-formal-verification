/-
# Weight - validator集合の重み関数と性質

Coq元ファイル: casper/coq/theories/Weight.v

## 概要
validator集合を重み値（その中のvalidatorのstake値の合計）に対応付ける関数 `wt` の
定義と性質を提供します。多くの結果は `∑` の性質と集合演算の集合論的性質から導かれます。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Casper.NatExt
import Casper.SetTheoryProps
import Casper.Validator

open BigOperators
open Finset

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable (stake : Validator → ℕ)

/-!
## 重み関数 wt の定義

validatorの集合の重みを、その中のvalidatorのstake値の合計として定義します。
-/

/--
validator集合の重み関数

Coq: `Definition wt (s:{set Validator}) : nat := (\sum_(v in s) stake.[st_fun v]).`
-/
def wt (s : Finset Validator) : ℕ := ∑ v ∈ s, stake v

/-!
## wt の基本性質
-/

/--
wtは常に非負（自然数なので自明）

Coq: `Lemma wt_nonneg s: wt s >= 0.`
-/
lemma wt_nonneg (s : Finset Validator) : wt stake s ≥ 0 := Nat.zero_le _

/--
空集合の重みは常に0

Coq: `Lemma wt_set0 : wt set0 = 0.`
-/
lemma wt_set0 : wt stake ∅ = 0 := by
  simp [wt]

/-!
## 包含関係と重みの順序
-/

/--
集合の包含関係は重みの順序を誘導する

Coq: `Lemma wt_inc_leq (s1 s2:{set Validator}): s1 \subset s2 -> wt s1 <= wt s2.`
-/
lemma wt_inc_leq (s1 s2 : Finset Validator) (h : s1 ⊆ s2) : wt stake s1 ≤ wt stake s2 := by
  unfold wt
  apply Finset.sum_le_sum_of_subset h

/--
等しい集合は同じ重みを持つ

Coq: `Lemma wt_eq (s1 s2:{set Validator}): s1 = s2 -> wt s1 = wt s2.`
-/
lemma wt_eq (s1 s2 : Finset Validator) (h : s1 = s2) : wt stake s1 = wt stake s2 := by
  rw [h]

/-!
## 集合演算と重み
-/

/--
交わりは可換

Coq: `Lemma wt_meetC (s1 s2:{set Validator}): wt (s1 :&: s2) = wt (s2 :&: s1).`
-/
lemma wt_meetC (s1 s2 : Finset Validator) : wt stake (s1 ∩ s2) = wt stake (s2 ∩ s1) := by
  simp [inter_comm]

/--
互いに素な2つの集合の和の重みは、それぞれの重みの和

Coq: `Lemma wt_join_disjoint (s1 s2:{set Validator}):
       [disjoint s1 & s2] -> wt (s1 :|: s2) = wt s1 + wt s2.`
-/
lemma wt_join_disjoint (s1 s2 : Finset Validator) (h : Disjoint s1 s2) :
    wt stake (s1 ∪ s2) = wt stake s1 + wt stake s2 := by
  unfold wt
  rw [Finset.sum_union h]

/--
2つの集合の差集合の重み

Coq: `Lemma wt_diff (s1 s2:{set Validator}):
       wt (s1 :\: s2) = wt s1 - wt (s1 :&: s2).`
-/
lemma wt_diff (s1 s2 : Finset Validator) :
    wt stake (s1 \ s2) = wt stake s1 - wt stake (s1 ∩ s2) := by
  -- s1 を (s1 ∩ s2) ∪ (s1 \ s2) に分割
  have h_partition : s1 = (s1 ∩ s2) ∪ (s1 \ s2) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    constructor
    · intro hx
      by_cases h : x ∈ s2
      · left; exact ⟨hx, h⟩
      · right; exact ⟨hx, h⟩
    · intro h
      cases h with
      | inl h => exact h.1
      | inr h => exact h.1
  -- disjoint を証明
  have h_disj : Disjoint (s1 ∩ s2) (s1 \ s2) := by
    apply Casper.SetTheoryProps.setID_disjoint
  -- wt の加法性を適用
  have h_sum : wt stake s1 = wt stake (s1 ∩ s2) + wt stake (s1 \ s2) := by
    rw [h_partition]
    rw [wt_join_disjoint stake (s1 ∩ s2) (s1 \ s2) h_disj]
  -- 引き算に変形
  omega

/--
2つの集合の和を分割の重みの和として表現

Coq: `Lemma wt_join_partition (s1 s2:{set Validator}):
       wt (s1 :|: s2) = wt (s1 :\: s2) + wt (s2 :\: s1) + wt (s1 :&: s2).`
-/
lemma wt_join_partition (s1 s2 : Finset Validator) :
    wt stake (s1 ∪ s2) = wt stake (s1 \ s2) + wt stake (s2 \ s1) + wt stake (s1 ∩ s2) := by
  -- setU_par を使用: s1 ∪ s2 = (s1 \ s2) ∪ (s2 \ s1) ∪ (s1 ∩ s2)
  have h_partition : s1 ∪ s2 = (s1 \ s2) ∪ (s2 \ s1) ∪ (s1 ∩ s2) := by
    apply Casper.SetTheoryProps.setU_par
  rw [h_partition]
  -- (s1 \ s2) と (s2 \ s1) が disjoint であることを証明
  have h_disj1 : Disjoint (s1 \ s2) (s2 \ s1) := by
    apply Casper.SetTheoryProps.setDD_disjoint
  -- wt_join_disjoint を適用
  rw [wt_join_disjoint stake (s1 \ s2) (s2 \ s1) h_disj1]
  -- ((s1 \ s2) ∪ (s2 \ s1)) と (s1 ∩ s2) が disjoint であることを証明
  have h_disj2 : Disjoint ((s1 \ s2) ∪ (s2 \ s1)) (s1 ∩ s2) := by
    apply Casper.SetTheoryProps.setDDI_disjoint
  -- wt_join_disjoint を再度適用
  rw [wt_join_disjoint stake ((s1 \ s2) ∪ (s2 \ s1)) (s1 ∩ s2) h_disj2]
  omega

/--
2つの集合の和の重みを集合の重みで表現

Coq: `Lemma wt_join (s1 s2:{set Validator}):
       wt (s1 :|: s2) = wt s1 + wt s2 - wt (s1 :&: s2).`
-/
lemma wt_join (s1 s2 : Finset Validator) :
    wt stake (s1 ∪ s2) = wt stake s1 + wt stake s2 - wt stake (s1 ∩ s2) := by
  -- wt_join_partition を使用
  rw [wt_join_partition]
  -- wt_diff を使って s1 \ s2 と s2 \ s1 を展開
  have h1 : wt stake (s1 \ s2) = wt stake s1 - wt stake (s1 ∩ s2) := by
    apply wt_diff
  have h2 : wt stake (s2 \ s1) = wt stake s2 - wt stake (s2 ∩ s1) := by
    apply wt_diff
  -- s1 ∩ s2 = s2 ∩ s1 を使用
  have h_comm : wt stake (s2 ∩ s1) = wt stake (s1 ∩ s2) := by
    apply wt_meetC
  rw [h1, h2, h_comm]
  -- 算術計算
  omega

/-!
## 交わりの重みに関する性質
-/

/--
交わりの重みは第1集合の重み以下

Coq: `Lemma wt_meet_leq1 (s1 s2:{set Validator}): wt (s1 :&: s2) <= wt s1.`
-/
lemma wt_meet_leq1 (s1 s2 : Finset Validator) : wt stake (s1 ∩ s2) ≤ wt stake s1 := by
  apply wt_inc_leq
  exact inter_subset_left

/--
交わりの重みは第2集合の重み以下

Coq: `Lemma wt_meet_leq2 (s1 s2:{set Validator}): wt (s1 :&: s2) <= wt s2.`
-/
lemma wt_meet_leq2 (s1 s2 : Finset Validator) : wt stake (s1 ∩ s2) ≤ wt stake s2 := by
  apply wt_inc_leq
  exact inter_subset_right

/--
交わりの重みは両集合の重みの和以下

Coq: `Lemma wt_meet_leq (s1 s2:{set Validator}):
       wt (s1 :&: s2) <= wt s1 + wt s2.`
-/
lemma wt_meet_leq (s1 s2 : Finset Validator) : wt stake (s1 ∩ s2) ≤ wt stake s1 + wt stake s2 := by
  have h1 := wt_meet_leq1 stake s1 s2
  have h2 := Nat.le_add_right (wt stake s1) (wt stake s2)
  exact Nat.le_trans h1 h2

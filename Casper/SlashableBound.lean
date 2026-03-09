/-
# SlashableBound - Slashable Bound定理

Coq元ファイル: casper/coq/theories/SlashableBound.v

## 概要
動的validator集合におけるSlashable Bound定理を証明します。
この定理は、2つの競合するブロックが両方k-finalizedされている場合、
スラッシングされるvalidatorの重みの下限を与えます。

## 注意事項
- この定理は、validatorの動的な参加（activation）と退出（exit）を考慮します。
- 重み関数（wt）に関する複雑な不等式を扱います。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Casper.NatExt
import Casper.SetTheoryProps
import Casper.Validator
import Casper.Weight
import Casper.HashTree
import Casper.State
import Casper.Slashing
import Casper.Quorums
import Casper.Justification
import Casper.AccountableSafety

open Finset
open Casper.NatExt

variable {Validator Hash : Type}
variable [Fintype Validator] [DecidableEq Validator]
variable [Fintype Hash] [DecidableEq Hash]
variable (hash_parent : Hash → Hash → Prop)
variable (genesis : Hash)
variable (stake : Validator → ℕ)
variable (vset : Hash → Finset Validator)

/-!
## Activation と Exit の定義
-/

/--
s1からs2の間にactivateされたvalidatorの集合

Coq: `Definition activated (s1 s2: {set Validator}): {set Validator} :=
      s2 :\: s1.`
-/
def activated (s1 s2 : Finset Validator) : Finset Validator :=
  s2 \ s1

/--
s1からs2の間にexitしたvalidatorの集合

Coq: `Definition exited (s1 s2: {set Validator}): {set Validator} :=
      s1 :\: s2.`
-/
def exited (s1 s2 : Finset Validator) : Finset Validator :=
  s1 \ s2

/--
s1からs2への新しいactivationの重み

Coq: `Definition actwt (s1 s2: {set Validator}): nat :=
      wt (activated s1 s2).`
-/
def actwt (s1 s2 : Finset Validator) : ℕ :=
  wt stake (activated s1 s2)

/--
s1からs2にexitしたvalidatorの重み

Coq: `Definition extwt (s1 s2: {set Validator}): nat :=
      wt (exited s1 s2).`
-/
def extwt (s1 s2 : Finset Validator) : ℕ :=
  wt stake (exited s1 s2)

/-!
## 重み関数に関する補助補題
-/

/--
集合の交わりの重み境界

Coq: `Lemma wt_meet_bound`

注意: この補題は集合論と算術の複雑な証明です。
-/
lemma wt_meet_bound :
    ∀ (s1 s2 s1' s2' : Finset Validator),
      s1 ⊆ s1' →
      s2 ⊆ s2' →
      let s12' := s1' ∩ s2'
      wt stake (s1 ∩ s2) + wt stake s12' ≥
        wt stake (s1 ∩ s12') + wt stake (s2 ∩ s12') := by
  intro s1 s2 s1' s2' Hs1sub Hs2sub s12'
  -- Hs1 : s1 ∩ s1' = s1 (s1 ⊆ s1' より)
  have Hs1 : s1 ∩ s1' = s1 := Finset.inter_eq_left.mpr Hs1sub
  -- Hs2 : s2 ∩ s2' = s2 (s2 ⊆ s2' より)
  have Hs2 : s2 ∩ s2' = s2 := Finset.inter_eq_left.mpr Hs2sub
  -- s1 ∩ s12' = s1 ∩ (s1' ∩ s2') = (s1 ∩ s1') ∩ s2' = s1 ∩ s2'
  have h1 : s1 ∩ s12' = s1 ∩ s2' := by
    simp only [s12', inter_assoc, Hs1]
  -- s2 ∩ s12' = s2 ∩ (s1' ∩ s2') = s2 ∩ s1' ∩ s2' = s2 ∩ s1' (s2 ⊆ s2')
  have h2 : s2 ∩ s12' = s2 ∩ s1' := by
    simp only [s12']
    rw [inter_comm s1' s2', inter_assoc, Hs2]
  -- 式を書き換え
  rw [h1, h2]
  -- s1 ∩ s2' を (s1 ∩ s2' ∩ s2) ∪ (s1 ∩ s2' \ s2) に分解
  have h_part1 : s1 ∩ s2' = (s1 ∩ s2' ∩ s2) ∪ (s1 ∩ s2' \ s2) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    constructor
    · intro ⟨hx1, hx2'⟩
      by_cases hx2 : x ∈ s2
      · left; exact ⟨⟨hx1, hx2'⟩, hx2⟩
      · right; exact ⟨⟨hx1, hx2'⟩, hx2⟩
    · intro h
      cases h with
      | inl h => exact ⟨h.1.1, h.1.2⟩
      | inr h => exact h.1
  have h_disj1 : Disjoint (s1 ∩ s2' ∩ s2) (s1 ∩ s2' \ s2) := by
    rw [disjoint_left]
    intro x hx1 hx2
    simp [mem_inter, mem_sdiff] at hx1 hx2
    exact hx2.2 hx1.2
  have h_wt1 : wt stake (s1 ∩ s2') = wt stake (s1 ∩ s2' ∩ s2) + wt stake (s1 ∩ s2' \ s2) := by
    rw [h_part1, wt_join_disjoint]
    exact h_disj1
  -- s2 ∩ s1' を (s2 ∩ s1' ∩ s1) ∪ (s2 ∩ s1' \ s1) に分解
  have h_part2 : s2 ∩ s1' = (s2 ∩ s1' ∩ s1) ∪ (s2 ∩ s1' \ s1) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    constructor
    · intro ⟨hx2, hx1'⟩
      by_cases hx1 : x ∈ s1
      · left; exact ⟨⟨hx2, hx1'⟩, hx1⟩
      · right; exact ⟨⟨hx2, hx1'⟩, hx1⟩
    · intro h
      cases h with
      | inl h => exact ⟨h.1.1, h.1.2⟩
      | inr h => exact h.1
  have h_disj2 : Disjoint (s2 ∩ s1' ∩ s1) (s2 ∩ s1' \ s1) := by
    rw [disjoint_left]
    intro x hx1 hx2
    simp [mem_inter, mem_sdiff] at hx1 hx2
    exact hx2.2 hx1.2
  have h_wt2 : wt stake (s2 ∩ s1') = wt stake (s2 ∩ s1' ∩ s1) + wt stake (s2 ∩ s1' \ s1) := by
    rw [h_part2, wt_join_disjoint]
    exact h_disj2
  -- (s1 ∩ s2' ∩ s2) = (s1 ∩ s2), (s2 ∩ s1' ∩ s1) = (s1 ∩ s2)
  have h_eq1 : s1 ∩ s2' ∩ s2 = s1 ∩ s2 := by
    ext x
    simp only [mem_inter]
    constructor
    · intro ⟨⟨hx1, _⟩, hx2⟩; exact ⟨hx1, hx2⟩
    · intro ⟨hx1, hx2⟩; exact ⟨⟨hx1, Hs2sub hx2⟩, hx2⟩
  have h_eq2 : s2 ∩ s1' ∩ s1 = s1 ∩ s2 := by
    ext x
    simp only [mem_inter]
    constructor
    · intro ⟨⟨hx2, _⟩, hx1⟩; exact ⟨hx1, hx2⟩
    · intro ⟨hx1, hx2⟩; exact ⟨⟨hx2, Hs1sub hx1⟩, hx1⟩
  rw [h_eq1] at h_wt1
  rw [h_eq2] at h_wt2
  rw [h_wt1, h_wt2]
  -- 不等式を証明: (s1 ∩ s2) + s12' ≥ (s1 ∩ s2) + (s1 ∩ s2' \ s2) + (s1 ∩ s2) + (s2 ∩ s1' \ s1)
  -- s12' ≥ (s1 ∩ s2' \ s2) + (s2 ∩ s1' \ s1) を示せばよい
  -- これは (s1 ∩ s2' \ s2) ∪ (s2 ∩ s1' \ s1) ⊆ s12' から従う
  have h_sub : (s1 ∩ s2' \ s2) ∪ (s2 ∩ s1' \ s1) ⊆ s12' := by
    intro x hx
    simp only [mem_union, mem_inter, mem_sdiff, s12'] at hx ⊢
    cases hx with
    | inl h => exact ⟨Hs1sub h.1.1, h.1.2⟩
    | inr h => exact ⟨h.1.2, Hs2sub h.1.1⟩
  have h_disj3 : Disjoint (s1 ∩ s2' \ s2) (s2 ∩ s1' \ s1) := by
    rw [disjoint_left]
    intro x hx1 hx2
    simp [mem_inter, mem_sdiff] at hx1 hx2
    exact hx1.2 hx2.1.1
  have h_wt_sub : wt stake ((s1 ∩ s2' \ s2) ∪ (s2 ∩ s1' \ s1)) ≤ wt stake s12' := by
    apply wt_inc_leq
    exact h_sub
  have h_wt_union : wt stake ((s1 ∩ s2' \ s2) ∪ (s2 ∩ s1' \ s1)) =
      wt stake (s1 ∩ s2' \ s2) + wt stake (s2 ∩ s1' \ s1) := by
    apply wt_join_disjoint
    exact h_disj3
  rw [h_wt_union] at h_wt_sub
  omega

/--
集合の交わりと差の重み境界

Coq: `Lemma wt_meet_subbound`
-/
lemma wt_meet_subbound :
    ∀ (s1 s1' s2' : Finset Validator),
      s1 ⊆ s1' →
      wt stake (s1 ∩ (s1' ∩ s2')) + wt stake (s1' \ s2') ≥ wt stake s1 := by
  intro s1 s1' s2' Hs1sub
  -- s1 ⊆ s1' より s1 ∩ s1' = s1
  have h_inter : s1 ∩ s1' = s1 := by
    ext x
    simp only [mem_inter]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h1; exact ⟨h1, Hs1sub h1⟩
  -- s1 ∩ (s1' ∩ s2') = (s1 ∩ s1') ∩ s2' = s1 ∩ s2'
  have h_assoc : s1 ∩ (s1' ∩ s2') = s1 ∩ s2' := by
    rw [inter_assoc, h_inter]
  rw [h_assoc]
  -- setID2_subset: s1 ⊆ (s1 ∩ s2') ∪ (s1' \ s2') を使用
  have h_subset : s1 ⊆ (s1 ∩ s2') ∪ (s1' \ s2') := by
    apply Casper.SetTheoryProps.setID2_subset
    exact Hs1sub
  -- setID2_disjoint: (s1 ∩ s2') と (s1' \ s2') は disjoint
  have h_disj : Disjoint (s1 ∩ s2') (s1' \ s2') := by
    apply Casper.SetTheoryProps.setID2_disjoint
  -- wt_join_disjoint を適用
  have h_union : wt stake ((s1 ∩ s2') ∪ (s1' \ s2')) = wt stake (s1 ∩ s2') + wt stake (s1' \ s2') := by
    apply wt_join_disjoint
    exact h_disj
  -- wt_inc_leq を適用
  rw [← h_union]
  apply wt_inc_leq
  exact h_subset

/--
3つの集合の差の重み三角不等式

Coq: `Lemma wt_meet_tri_bound`
-/
lemma wt_meet_tri_bound :
    ∀ (s0 s1 s2 : Finset Validator),
      wt stake (s1 \ s2) ≤ wt stake (s0 \ s2) + wt stake (s1 \ s0) := by
  intro s0 s1 s2
  -- set3D_subset: s1 \ s2 ⊆ (s0 \ s2) ∪ (s1 \ s0) を使用
  have h_subset : s1 \ s2 ⊆ (s0 \ s2) ∪ (s1 \ s0) := by
    apply Casper.SetTheoryProps.set3D_subset
  -- set3D_disjoint: (s0 \ s2) と (s1 \ s0) は disjoint
  have h_disj : Disjoint (s0 \ s2) (s1 \ s0) := by
    apply Casper.SetTheoryProps.set3D_disjoint
  -- wt_join_disjoint を適用
  have h_union : wt stake ((s0 \ s2) ∪ (s1 \ s0)) = wt stake (s0 \ s2) + wt stake (s1 \ s0) := by
    apply wt_join_disjoint
    exact h_disj
  -- wt_inc_leq を適用
  rw [← h_union]
  apply wt_inc_leq
  exact h_subset

/-!
## メイン定理
-/

/--
Slashable Bound定理

動的validator集合において、2つの競合するブロックが両方k-finalizedされている場合、
スラッシングされるvalidatorの重みの下限を与えます。

Coq: `Theorem slashable_bound`

この定理は、あるベースブロックb0を基準として、
2つの競合するk-finalizedブロックb1とb2について、
スラッシングされるvalidatorの交わりの重みが、
activation/exit weightとquorum weightから計算される下限以上であることを示します。
-/
theorem slashable_bound :
    ∀ (st : State Validator Hash) (b0 b1 b2 : Hash) (b1_h b2_h : ℕ) (k1 k2 : ℕ),
      k_finalized hash_parent stake vset st b1 b1_h k1 →
      k_finalized hash_parent stake vset st b2 b2_h k2 →
      ¬ hash_ancestor hash_parent b1 b2 →
      ¬ hash_ancestor hash_parent b2 b1 →
      ∃ (bL bR : Hash) (qL qR : Finset Validator),
        let v0 := vset b0
        let vL := vset bL
        let vR := vset bR
        let aL := actwt stake v0 vL
        let eL := extwt stake v0 vL
        let aR := actwt stake v0 vR
        let eR := extwt stake v0 vR
        let xM := max (wt stake vL - aL - eR) (wt stake vR - aR - eL)
        qL ⊆ vL ∧
        qR ⊆ vR ∧
        wt stake (qL ∩ qR) ≥ xM - one_third (wt stake vL) - one_third (wt stake vR) := by
  intro st b0 b1 b2 b1_h b2_h k1 k2 Hb1f Hb2f Hconf1 Hconf2

  -- k_safety'からqL, qRとスラッシング情報を取得
  obtain ⟨bL, bR, qL, qR, HqLsubset, HqRsubset, HqLq2, HqRq2, Hqslashed⟩ :=
    k_safety' hash_parent genesis stake vset st b1 b1_h b2 b2_h k1 k2
      Hb1f Hb2f Hconf2 Hconf1

  clear Hb1f Hb2f Hconf2 Hconf1
  use bL, bR, qL, qR

  -- 変数の定義
  let v0 := vset b0
  let vL := vset bL
  let vR := vset bR
  let aL := actwt stake v0 vL
  let eR := extwt stake v0 vR
  let aR := actwt stake v0 vR
  let eL := extwt stake v0 vL
  let vLR := vL ∩ vR

  constructor
  · exact HqLsubset
  constructor
  · exact HqRsubset

  -- メインの不等式証明
  -- この証明は、以下のステップで進みます：
  -- 1. wt_meet_boundを使用して基本的な境界を設定
  -- 2. wt_meet_subboundを使用してqL, qRの境界を精密化
  -- 3. quorum_2の定義から、qLとqRが2/3以上の重みを持つことを使用
  -- 4. activation/exit weightの関係を使用して最終的な境界を導出

  have Hbound := wt_meet_bound stake qL qR vL vR HqLsubset HqRsubset
  have HsubL := wt_meet_subbound stake qL vL vR HqLsubset
  have HsubR := wt_meet_subbound stake qR vR vL HqRsubset

  -- quorum_2の条件を展開
  unfold quorum_2 at HqLq2 HqRq2
  obtain ⟨_, HqLwt⟩ := HqLq2
  obtain ⟨_, HqRwt⟩ := HqRq2

  -- 変数置き換えを明示
  change wt stake qL ≥ two_third (wt stake vL) at HqLwt
  change wt stake qR ≥ two_third (wt stake vR) at HqRwt

  -- HsubL と HsubR を足して結合
  have HsubLR : wt stake qL + wt stake qR ≤
      wt stake (qL ∩ vLR) + wt stake (vL \ vR) +
      (wt stake (qR ∩ vLR) + wt stake (vR \ vL)) := by
    have h1 := HsubL
    have h2 := HsubR
    -- qR ∩ (vR ∩ vL) = qR ∩ vLR を示す
    have h_comm : qR ∩ (vR ∩ vL) = qR ∩ vLR := by
      ext x
      simp only [mem_inter, vLR]
      constructor
      · intro ⟨hqR, hvR, hvL⟩
        exact ⟨hqR, hvL, hvR⟩
      · intro ⟨hqR, hvL, hvR⟩
        exact ⟨hqR, hvR, hvL⟩
    rw [h_comm] at h2
    omega

  -- Hboundの不等式を整理
  -- Hbound: wt (qL ∩ qR) + wt vLR ≥ wt (qL ∩ vLR) + wt (qR ∩ vLR)
  have Hbound_rw : wt stake (qL ∩ vLR) + wt stake (qR ∩ vLR) ≤
      wt stake (qL ∩ qR) + wt stake vLR := by
    have h := Hbound
    omega

  -- 結合して新しい境界を得る
  have Hbound' : wt stake qL + wt stake qR ≤
      wt stake (qL ∩ qR) + wt stake vLR +
      wt stake (vL \ vR) + wt stake (vR \ vL) := by
    calc wt stake qL + wt stake qR
        ≤ wt stake (qL ∩ vLR) + wt stake (vL \ vR) +
          (wt stake (qR ∩ vLR) + wt stake (vR \ vL)) := HsubLR
      _ = wt stake (qL ∩ vLR) + wt stake (qR ∩ vLR) +
          wt stake (vL \ vR) + wt stake (vR \ vL) := by omega
      _ ≤ wt stake (qL ∩ qR) + wt stake vLR +
          wt stake (vL \ vR) + wt stake (vR \ vL) := by omega

  -- wt_join_partition を使って vL ∪ vR の重みを表現
  have H_join_part : wt stake (vL ∪ vR) =
      wt stake (vL \ vR) + wt stake (vR \ vL) + wt stake vLR := by
    have h := wt_join_partition stake vL vR
    simp only [vLR]
    omega

  -- wt_join を使って vL ∪ vR の重みを別の形で表現
  have H_join : wt stake (vL ∪ vR) = wt stake vL + wt stake vR - wt stake vLR := by
    have h := wt_join stake vL vR
    simp only [vLR]
    exact h

  -- これら2つの等式から
  have H_eq : wt stake vLR + wt stake (vL \ vR) + wt stake (vR \ vL) =
      wt stake vL + wt stake vR - wt stake vLR := by
    have h1 := H_join_part
    have h2 := H_join
    omega

  -- Hbound'を書き換え
  have Hbound'' : wt stake qL + wt stake qR ≤
      wt stake (qL ∩ qR) + wt stake vL + wt stake vR - wt stake vLR := by
    calc wt stake qL + wt stake qR
        ≤ wt stake (qL ∩ qR) + wt stake vLR +
          wt stake (vL \ vR) + wt stake (vR \ vL) := Hbound'
      _ = wt stake (qL ∩ qR) +
          (wt stake vLR + wt stake (vL \ vR) + wt stake (vR \ vL)) := by omega
      _ = wt stake (qL ∩ qR) +
          (wt stake vL + wt stake vR - wt stake vLR) := by rw [H_eq]
      _ = wt stake (qL ∩ qR) + wt stake vL + wt stake vR - wt stake vLR := by
          have h_meet_leq : wt stake vLR ≤ wt stake vL + wt stake vR := by
            apply wt_meet_leq
          omega

  -- quorumの重み条件を適用
  have HqLR : two_third (wt stake vL) + two_third (wt stake vR) ≤
      wt stake qL + wt stake qR := by
    omega

  -- 結合
  have Hbound3 : two_third (wt stake vL) + two_third (wt stake vR) ≤
      wt stake (qL ∩ qR) + wt stake vL + wt stake vR - wt stake vLR := by
    calc two_third (wt stake vL) + two_third (wt stake vR)
        ≤ wt stake qL + wt stake qR := HqLR
      _ ≤ wt stake (qL ∩ qR) + wt stake vL + wt stake vR - wt stake vLR := Hbound''

  -- thirds_def を適用: n - two_third n = one_third n
  -- 整理して最終形を得る
  have H_thirds_L := thirds_def (wt stake vL)
  have H_thirds_R := thirds_def (wt stake vR)
  have H_leq_two_L := leq_two_thirds (wt stake vL)
  have H_leq_two_R := leq_two_thirds (wt stake vR)

  -- wt_diff と wt_meet_tri_bound を使って vLR の下限を得る

  -- vL \ vR = wt vL - wt (vL ∩ vR) = wt vL - wt vLR
  have HxL : wt stake (vL \ vR) = wt stake vL - wt stake vLR := by
    have h := wt_diff stake vL vR
    simp only [vLR] at h ⊢
    exact h

  -- wt_meet_tri_bound: wt (vL \ vR) ≤ wt (v0 \ vR) + wt (vL \ v0)
  have HxLbound := wt_meet_tri_bound stake v0 vL vR
  -- wt (v0 \ vR) = eR, wt (vL \ v0) = aL
  -- eR = extwt v0 vR = wt (exited v0 vR) = wt (v0 \ vR)
  -- aL = actwt v0 vL = wt (activated v0 vL) = wt (vL \ v0)

  -- 同様に vR \ vL について
  have HxR : wt stake (vR \ vL) = wt stake vR - wt stake (vR ∩ vL) := by
    have h := wt_diff stake vR vL
    exact h

  have HxRbound := wt_meet_tri_bound stake v0 vR vL

  -- vLR = vL ∩ vR, vR ∩ vL = vLR
  have H_vLR_comm : wt stake (vR ∩ vL) = wt stake vLR := by
    simp only [vLR]
    exact wt_meetC stake vR vL

  -- HxL から: wt vLR = wt vL - wt (vL \ vR)
  have H_vLR_from_L : wt stake vLR = wt stake vL - wt stake (vL \ vR) := by
    have h := HxL
    have h_leq : wt stake vLR ≤ wt stake vL := wt_meet_leq1 stake vL vR
    omega

  -- HxLbound と組み合わせて: wt vLR ≥ wt vL - (wt (v0 \ vR) + wt (vL \ v0))
  --                       = wt vL - eR - aL
  have H_vLR_bound_L : wt stake vLR ≥ wt stake vL - eR - aL := by
    have h1 := H_vLR_from_L
    have h2 := HxLbound
    -- eR = wt (v0 \ vR), aL = wt (vL \ v0)
    simp only [eR, aL, extwt, exited, actwt, activated] at h2 ⊢
    omega

  -- 同様に HxR と HxRbound から
  have H_vLR_from_R : wt stake vLR = wt stake vR - wt stake (vR \ vL) := by
    have h := HxR
    have h_leq : wt stake (vR ∩ vL) ≤ wt stake vR := wt_meet_leq1 stake vR vL
    rw [H_vLR_comm]
    omega

  have H_vLR_bound_R : wt stake vLR ≥ wt stake vR - eL - aR := by
    have h1 := H_vLR_from_R
    have h2 := HxRbound
    simp only [eL, aR, extwt, exited, actwt, activated] at h2 ⊢
    omega

  -- max の定義を使う
  have HxM : wt stake vLR ≥ max (wt stake vL - aL - eR) (wt stake vR - aR - eL) := by
    rw [Nat.max_def]
    split_ifs with h
    · -- (wt stake vL - aL - eR) ≤ (wt stake vR - aR - eL) の場合
      exact H_vLR_bound_R
    · -- そうでない場合
      exact H_vLR_bound_L

  -- 最終的な不等式を導出
  -- 目標: wt (qL ∩ qR) ≥ xM - one_third (wt vL) - one_third (wt vR)
  -- ここで xM = max (wt vL - aL - eR) (wt vR - aR - eL)

  -- Hbound3から:
  -- two_third (wt vL) + two_third (wt vR) ≤ wt (qL ∩ qR) + wt vL + wt vR - wt vLR
  -- 整理して:
  -- wt vLR ≤ wt (qL ∩ qR) + wt vL + wt vR - two_third (wt vL) - two_third (wt vR)
  -- wt vLR ≤ wt (qL ∩ qR) + one_third (wt vL) + one_third (wt vR)
  -- wt vLR - one_third (wt vL) - one_third (wt vR) ≤ wt (qL ∩ qR)

  have Hfinal : wt stake vLR - one_third (wt stake vL) - one_third (wt stake vR) ≤
      wt stake (qL ∩ qR) := by
    have h3 := Hbound3
    -- two_third + two_third ≤ wt (qL ∩ qR) + wt vL + wt vR - wt vLR
    -- wt vLR ≤ wt (qL ∩ qR) + wt vL + wt vR - two_third (wt vL) - two_third (wt vR)
    -- = wt (qL ∩ qR) + (wt vL - two_third (wt vL)) + (wt vR - two_third (wt vR))
    -- = wt (qL ∩ qR) + one_third (wt vL) + one_third (wt vR)
    have h_expand : wt stake vL + wt stake vR - two_third (wt stake vL) - two_third (wt stake vR) =
        one_third (wt stake vL) + one_third (wt stake vR) := by
      have h1 := H_thirds_L
      have h2 := H_thirds_R
      omega
    omega

  -- HxM: wt vLR ≥ xM を使って
  -- xM - one_third (wt vL) - one_third (wt vR) ≤ wt vLR - one_third (wt vL) - one_third (wt vR)
  --                                           ≤ wt (qL ∩ qR)
  calc max (wt stake vL - aL - eR) (wt stake vR - aR - eL) -
          one_third (wt stake vL) - one_third (wt stake vR)
      ≤ wt stake vLR - one_third (wt stake vL) - one_third (wt stake vR) := by
        omega
    _ ≤ wt stake (qL ∩ qR) := Hfinal

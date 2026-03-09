/-
# AccountableSafety - Accountable Safety定理

Coq元ファイル: casper/coq/theories/AccountableSafety.v

## 概要
Gasper protocolにおけるAccountable Safety定理を証明します。
この定理は、2つの競合するブロックが両方finalizedされる場合、
少なくとも1/3のstakeがスラッシングされることを保証します。

## 翻訳上の注意
- CoqHammerの`Reconstr.scrush`と`Reconstr.hobvious`を使用した証明は、
  Lean4では手動で証明を展開しています。
- カスタムタクティク`spec`は各使用箇所で手動展開しています。
- Classical推論(`classic`)は`Classical.em`を使用します。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic
import Casper.StrongInductionLtn
import Casper.Validator
import Casper.Weight
import Casper.HashTree
import Casper.State
import Casper.Slashing
import Casper.Quorums
import Casper.Justification

open Casper.StrongInductionLtn
open Classical
open Finset

variable {Validator Hash : Type}
variable [Fintype Validator] [DecidableEq Validator]
variable [Fintype Hash] [DecidableEq Hash]
variable (hash_parent : Hash → Hash → Prop)
variable (genesis : Hash)
variable (stake : Validator → ℕ)
variable (vset : Hash → Finset Validator)

/-!
## Finalization forkの定義
-/

/--
Finalization forkは、2つの競合するブロックが両方finalizedされている状態

Coq: `Definition finalization_fork st :=
      exists b1 b1_h b2 b2_h,
        finalized st b1 b1_h /\
        finalized st b2 b2_h /\
        b2 </~* b1 /\ b1 </~* b2.`
-/
def finalization_fork (st : State Validator Hash) : Prop :=
  ∃ (b1 : Hash) (b1_h : ℕ) (b2 : Hash) (b2_h : ℕ),
    finalized hash_parent stake vset st b1 b1_h ∧
    finalized hash_parent stake vset st b2 b2_h ∧
    ¬ hash_ancestor hash_parent b2 b1 ∧
    ¬ hash_ancestor hash_parent b1 b2

/--
異なる深さでのfinalization fork

Coq: `Definition k_finalization_fork st k1 k2 :=
      exists b1 b1_h b2 b2_h,
        k_finalized st b1 b1_h k1 /\
        k_finalized st b2 b2_h k2 /\
        b2 </~* b1 /\ b1 </~* b2.`
-/
def k_finalization_fork (st : State Validator Hash) (k1 k2 : ℕ) : Prop :=
  ∃ (b1 : Hash) (b1_h : ℕ) (b2 : Hash) (b2_h : ℕ),
    k_finalized hash_parent stake vset st b1 b1_h k1 ∧
    k_finalized hash_parent stake vset st b2 b2_h k2 ∧
    ¬ hash_ancestor hash_parent b2 b1 ∧
    ¬ hash_ancestor hash_parent b1 b2

/--
同じ深さでのfinalization fork

Coq: `Definition same_k_finalization_fork st k :=
      k_finalization_fork st k k.`
-/
def same_k_finalization_fork (st : State Validator Hash) (k : ℕ) : Prop :=
  k_finalization_fork hash_parent stake vset st k k

/-!
## 基本補題
-/

/--
finalization_fork <-> same_k_finalization_fork at depth 1

Coq: `Lemma finalization_fork_means_same_finalization_fork_one`
-/
lemma finalization_fork_means_same_finalization_fork_one :
    ∀ (st : State Validator Hash),
      finalization_fork hash_parent stake vset st ↔
      same_k_finalization_fork hash_parent stake vset st 1 := by
  intro st
  constructor
  · -- →方向
    intro ⟨b1, b1_h, b2, b2_h, Hfin1, Hfin2, Hnot1, Hnot2⟩
    use b1, b1_h, b2, b2_h
    constructor
    · exact finalized_means_one_finalized hash_parent stake vset st b1 b1_h |>.mp Hfin1
    constructor
    · exact finalized_means_one_finalized hash_parent stake vset st b2 b2_h |>.mp Hfin2
    constructor
    · exact Hnot1
    · exact Hnot2
  · -- ←方向
    intro ⟨b1, b1_h, b2, b2_h, Hfin1, Hfin2, Hnot1, Hnot2⟩
    use b1, b1_h, b2, b2_h
    constructor
    · exact finalized_means_one_finalized hash_parent stake vset st b1 b1_h |>.mpr Hfin1
    constructor
    · exact finalized_means_one_finalized hash_parent stake vset st b2 b2_h |>.mpr Hfin2
    constructor
    · exact Hnot1
    · exact Hnot2

/--
2つの異なるブロックが同じ高さでjustifiedされることはない（quorumがスラッシングされない限り）

Coq: `Lemma no_two_justified_same_height`

注意: この証明は元のCoqコードで`Reconstr.scrush`を使用しています。
-/
lemma no_two_justified_same_height :
    ∀ (st : State Validator Hash) (b1 : Hash) (b1_h : ℕ) (b2 : Hash) (b2_h : ℕ),
      justified hash_parent stake vset st b1 b1_h →
      justified hash_parent stake vset st b2 b2_h →
      ¬ q_intersection_slashed stake vset st →
      b1 ≠ b2 →
      b1_h ≠ b2_h := by
  intro st b1 b1_h b2 b2_h Hj1 Hj2 Hs Hneq
  -- b1とb2のjustificationを分析
  cases Hj1 with
  | genesis =>
      -- b1がgenesisの場合、b1_h = 0
      cases Hj2 with
      | genesis => contradiction
      | link s2 s2_h t2 t2_h Hjs2 Hjl2 =>
          -- t2 = b2, t2_h = b2_h
          -- Hjl2より t2_h > s2_h なので b2_h >= 1
          -- b1_h = 0 なので b1_h ≠ b2_h
          obtain ⟨Hh2, _, _⟩ := Hjl2
          -- Hh2 : t2_h > s2_h, すなわち b2_h > s2_h >= 0 より b2_h >= 1
          -- b1_h = 0 なので b1_h ≠ b2_h
          omega
  | link s1 s1_h t1 t1_h Hjs1 Hjl1 =>
      -- b1がjustification linkの場合
      cases Hj2 with
      | genesis =>
          -- b2 = genesis, b2_h = 0
          -- Hjl1より t1_h > s1_h なので b1_h >= 1
          -- b1_h >= 1 ≠ 0 = b2_h
          obtain ⟨Hh1, _, _⟩ := Hjl1
          omega
      | link s2 s2_h t2 t2_h Hjs2 Hjl2 =>
          -- 両方がjustification linkの場合
          obtain ⟨Hh1, Ha1, Hsm1⟩ := Hjl1
          obtain ⟨Hh2, Ha2, Hsm2⟩ := Hjl2
          intro heq
          -- 高さが等しいと仮定
          subst heq
          apply Hs
          -- q_intersection_slashedを構成
          use b1, b2
          let vL := link_supporters st s1 b1 s1_h b2_h
          let vR := link_supporters st s2 b2 s2_h b2_h
          use vL, vR
          constructor
          · -- vL ⊆ vset b1
            unfold quorum_2 at Hsm1
            exact Hsm1.1
          constructor
          · -- vR ⊆ vset b2
            unfold quorum_2 at Hsm2
            exact Hsm2.1
          constructor
          · -- quorum_2 vL b1
            exact Hsm1
          constructor
          · -- quorum_2 vR b2
            exact Hsm2
          · -- ∀ v ∈ vL ∩ vR → slashed st v
            intro v hvL hvR
            left  -- slashed_double_vote
            use b1, b2
            constructor
            · exact Hneq
            · use s1, s1_h, s2, s2_h, b2_h
              constructor
              · unfold link_supporters at hvL
                simp [Finset.mem_filter] at hvL
                exact hvL.2
              · unfold link_supporters at hvR
                simp [Finset.mem_filter] at hvR
                exact hvR.2

/--
ブロックがk-finalizedされている高さで、
別のブロックがjustifiedされることはない（quorumがスラッシングされない限り）

Coq: `Lemma no_k_finalized_justified_same_height`
-/
lemma no_k_finalized_justified_same_height :
    ∀ (st : State Validator Hash) (bf : Hash) (bf_h : ℕ) (bj : Hash) (bj_h : ℕ) (k : ℕ),
      k_finalized hash_parent stake vset st bf bf_h k →
      justified hash_parent stake vset st bj bj_h →
      ¬ q_intersection_slashed stake vset st →
      bj ≠ bf →
      bj_h ≠ bf_h := by
  intro st bf bf_h bj bj_h k Hkfin Hjust Hslash Hneq
  have Hjust_bf := k_finalized_means_justified hash_parent stake vset st bf bf_h k Hkfin
  exact no_two_justified_same_height hash_parent stake vset st bj bj_h bf bf_h
    Hjust Hjust_bf Hslash Hneq

/--
Surround slashing case（一般形）

Coq: `Lemma k_slash_surround_case_general`

注意: この補題は非常に複雑で、元のCoqコードでは300行以上にわたります。
-/
lemma k_slash_surround_case_general :
    ∀ (st : State Validator Hash) (s t final : Hash) (s_h t_h final_h : ℕ) (k : ℕ),
      justified hash_parent stake vset st s s_h →
      justification_link hash_parent stake vset st s t s_h t_h →
      k_finalized hash_parent stake vset st final final_h k →
      final_h < t_h →
      ¬ hash_ancestor hash_parent final t →
      s_h < final_h →
      q_intersection_slashed stake vset st := by
  intro st s t final s_h t_h final_h k Hsj Hjl Hfinal Hft Hnoans Hsf
  obtain ⟨Htgts, Hnth, Hsm⟩ := Hjl
  obtain ⟨H_k, ls, H_size, H_hd, H_rel, H_link⟩ := Hfinal
  -- 高さの比較を3通りに分ける
  have h_trichotomy : final_h + k < t_h ∨ final_h + k = t_h ∨ final_h + k > t_h := by
    omega
  cases h_trichotomy with
  | inl h_lt =>
      -- Full containment case
      use t, ls.getLast?.getD final
      let vL := link_supporters st s t s_h t_h
      let vR := link_supporters st final (ls.getLast?.getD final) final_h (final_h + k)
      use vL, vR
      constructor
      · unfold quorum_2 at Hsm
        exact Hsm.1
      constructor
      · unfold quorum_2 at H_link
        exact H_link.1
      constructor
      · exact Hsm
      constructor
      · exact H_link
      · -- ∀ v ∈ vL ∩ vR → slashed st v
        intro v hvL hvR
        right  -- slashed_surround_vote
        use s, t, s_h, t_h
        use final, ls.getLast?.getD final, final_h, final_h + k
        unfold link_supporters at hvL hvR
        simp [Finset.mem_filter] at hvL hvR
        constructor
        · exact hvL.2
        constructor
        · exact hvR.2
        constructor
        · exact Hsf
        · exact h_lt
  | inr h_ge =>
      cases h_ge with
      | inl h_eq =>
          -- Partial containment - equal case
          -- t = last final ls かどうかで分岐
          by_cases heq_t : t = ls.getLast?.getD final
          · -- t = last の場合、矛盾を導く
            have Hfinal_anc : hash_ancestor hash_parent final (ls.getLast?.getD final) := by
              -- H_rel k から nth_ancestor k final (ls.getD k final) を取得
              have h_rel_k := H_rel k (Nat.le_refl k)
              have h_nth := h_rel_k.2  -- nth_ancestor k final (ls.getD k final)
              -- ls.length = k + 1 より、ls.getLast?.getD final = ls.getD k final
              have h_eq : ls.getLast?.getD final = ls.getD k final := by
                simp only [List.getLast?, List.getD]
                cases hls : ls with
                | nil => simp at H_size
                | cons hd tl =>
                    simp only [List.length_cons] at H_size
                    have h_len_tl : tl.length = k := by omega
                    -- k >= 1 より tl.length >= 1 なので tl は空でない
                    cases htl : tl with
                    | nil =>
                        simp at h_len_tl
                        omega  -- k >= 1 だが tl.length = 0 は矛盾
                    | cons hd2 tl2 =>
                        simp [List.getLast?, List.getD]
                        -- 再帰的にリストの末尾を取得
                        induction k with
                        | zero => omega  -- k >= 1 だが k = 0 は矛盾
                        | succ k' ih =>
                            simp [List.getD]
                            simp only [List.length_cons] at h_len_tl
                            have : tl2.length = k' := by omega
                            -- List.getLast (hd2 :: tl2) と List.get に関する等式
                            rw [← htl]
                            simp [List.getLast, List.get?]
                            have h_get : tl.get? k' = tl.getLast? := by
                              rw [htl]
                              simp only [List.getLast?]
                              rw [List.get?_eq_get (by simp [htl]; omega)]
                              congr 1
                              simp [List.length, htl, this]
                              omega
                            simp [h_get, Option.getD]
                            cases htl' : tl.getLast? with
                            | none =>
                                rw [htl] at htl'
                                simp at htl'
                            | some v => rfl
              rw [h_eq]
              exact nth_ancestor_ancestor hash_parent k final (ls.getD k final) h_nth
            rw [← heq_t] at Hfinal_anc
            contradiction
          · -- t ≠ last の場合
            by_cases hqs : q_intersection_slashed stake vset st
            · exact hqs
            · -- q_intersection_slashedでない場合、矛盾を導く
              have Hjj : justified hash_parent stake vset st t t_h := by
                apply justified.link
                · exact Hsj
                · exact ⟨Htgts, Hnth, Hsm⟩
              have Hjlast : justified hash_parent stake vset st (ls.getD k final) (final_h + k) := by
                have h_rel_k := H_rel k (Nat.le_refl k)
                exact h_rel_k.1
              have Hneq_height := no_two_justified_same_height hash_parent stake vset st
                t t_h (ls.getD k final) (final_h + k) Hjj Hjlast hqs
              have h_neq : t ≠ ls.getD k final := by
                -- heq_t : t ≠ ls.getLast?.getD final
                -- ls.getLast?.getD final = ls.getD k final を証明
                have h_last_eq : ls.getLast?.getD final = ls.getD k final := by
                  simp only [List.getLast?, List.getD]
                  cases hls : ls with
                  | nil => simp at H_size
                  | cons hd tl =>
                      simp only [List.length_cons] at H_size
                      have h_len_tl : tl.length = k := by omega
                      cases htl : tl with
                      | nil =>
                          simp at h_len_tl
                          omega  -- k >= 1 だが tl.length = 0 は矛盾
                      | cons hd2 tl2 =>
                          simp [List.getLast?, List.getD]
                          induction k with
                          | zero => omega  -- k >= 1 だが k = 0 は矛盾
                          | succ k' ih =>
                              simp [List.getD]
                              simp only [List.length_cons] at h_len_tl
                              have : tl2.length = k' := by omega
                              rw [← htl]
                              simp [List.getLast, List.get?]
                              have h_get : tl.get? k' = tl.getLast? := by
                                rw [htl]
                                simp only [List.getLast?]
                                rw [List.get?_eq_get (by simp [htl]; omega)]
                                congr 1
                                simp [List.length, htl, this]
                                omega
                              simp [h_get, Option.getD]
                              cases htl' : tl.getLast? with
                              | none =>
                                  rw [htl] at htl'
                                  simp at htl'
                              | some v => rfl
                rw [h_last_eq] at heq_t
                exact heq_t
              have : t_h ≠ final_h + k := Hneq_height h_neq
              rw [h_eq] at this
              contradiction
      | inr h_gt =>
          -- Partial containment - greater case: final_h + k > t_h
          -- H_rel (t_h - final_h) を適用
          have h_diff_le_k : t_h - final_h ≤ k := by
            -- h_gt: final_h + k > t_h より
            omega
          have h_rel_diff := H_rel (t_h - final_h) h_diff_le_k
          obtain ⟨Hjust_diff, Hanc_diff⟩ := h_rel_diff
          -- final_h + (t_h - final_h) = t_h を証明 (Hft: final_h < t_h より)
          have h_height_eq : final_h + (t_h - final_h) = t_h := by omega
          -- ls.getD (t_h - final_h) final が t_h の高さで justified
          rw [h_height_eq] at Hjust_diff
          -- t = ls.getD (t_h - final_h) final かどうかで場合分け
          by_cases heq_t' : t = ls.getD (t_h - final_h) final
          · -- t = ls.getD (t_h - final_h) final の場合
            -- final <~* t となり、Hnoans と矛盾
            have Hfinal_anc' : hash_ancestor hash_parent final t := by
              rw [heq_t']
              exact nth_ancestor_ancestor hash_parent (t_h - final_h) final
                (ls.getD (t_h - final_h) final) Hanc_diff
            contradiction
          · -- t ≠ ls.getD (t_h - final_h) final の場合
            -- no_two_justified_same_height を適用
            by_cases hqs : q_intersection_slashed stake vset st
            · exact hqs
            · -- q_intersection_slashedでない場合、矛盾を導く
              have Hjj : justified hash_parent stake vset st t t_h := by
                apply justified.link
                · exact Hsj
                · exact ⟨Htgts, Hnth, Hsm⟩
              have Hneq_height' := no_two_justified_same_height hash_parent stake vset st
                t t_h (ls.getD (t_h - final_h) final) t_h Hjj Hjust_diff hqs heq_t'
              -- t_h ≠ t_h は矛盾
              exact absurd rfl Hneq_height'

/--
高さが異なる場合のsafety証明（帰納ステップ）

Coq: `Lemma k_non_equal_height_case_ind`

注意: この補題はstrong inductionを使用します。
-/
lemma k_non_equal_height_case_ind :
    ∀ (st : State Validator Hash) (b1 : Hash) (b1_h : ℕ) (b2 : Hash) (b2_h : ℕ) (k : ℕ),
      justified hash_parent stake vset st b1 b1_h →
      k_finalized hash_parent stake vset st b2 b2_h k →
      ¬ hash_ancestor hash_parent b2 b1 →
      b1_h > b2_h →
      q_intersection_slashed stake vset st := by
  intro st b1 b1_h b2 b2_h k Hb1j Hb2f Hconfl Hh
  -- Strong inductionを適用
  let P := fun (h1_h : ℕ) (h1 : Hash) =>
    justified hash_parent stake vset st h1 h1_h →
    k_finalized hash_parent stake vset st b2 b2_h k →
    ¬ hash_ancestor hash_parent b2 h1 →
    b2_h < h1_h →
    q_intersection_slashed stake vset st
  suffices hsuff : ∀ h1_h h1, P h1_h h1 by
    exact hsuff b1_h b1 Hb1j Hb2f Hconfl Hh
  have := strong_induction_sub (k := b2_h) (P := P)
  apply this
  intro b1_h' b1' IH Hb1j' Hb2f' Hconfl' Hh'
  -- b1'がgenesisかjustification linkか
  cases Hb1j' with
  | genesis =>
      -- genesisの場合、高さは0なので矛盾
      simp at Hh'
      omega
  | link s s_h Hjust_s Hjl =>
      -- justification linkの場合
      by_cases hqs : q_intersection_slashed stake vset st
      · exact hqs
      · -- q_intersection_slashedでない場合
        obtain ⟨Hsh, Hsa, Hsm⟩ := Hjl
        -- IHを適用するための準備
        have Hp : ¬ hash_ancestor hash_parent b2 s := by
          have Hm := nth_ancestor_ancestor hash_parent _ _ _ Hsa
          exact hash_ancestor_conflict hash_parent _ _ _ Hm Hconfl'
        have Hpneq : b2 ≠ s := hash_nonancestor_nonequal hash_parent _ _ Hp
        have Hpneq' : s ≠ b2 := Hpneq.symm
        have Hplt : s_h - b2_h < b1_h' - b2_h := by omega
        -- 場合分け: b2_h < s_h
        by_cases hlt : b2_h < s_h
        · -- b2_h < s_hの場合、IHを適用
          have h_k_lt : b2_h < s_h := hlt
          exact IH s_h s h_k_lt Hplt Hjust_s Hb2f' Hp hlt
        · -- b2_h ≥ s_hの場合
          push_neg at hlt
          by_cases heq : b2_h = s_h
          · -- b2_h = s_hの場合、矛盾
            have := no_k_finalized_justified_same_height hash_parent stake vset st
              b2 b2_h s s_h k Hb2f' Hjust_s hqs Hpneq'
            contradiction
          · -- b2_h > s_hの場合、surround slashing
            have hgt : s_h < b2_h := by omega
            exact k_slash_surround_case_general hash_parent genesis stake vset st
              s b1' b2 s_h b1_h' b2_h k Hjust_s ⟨Hsh, Hsa, Hsm⟩ Hb2f' Hh' Hconfl' hgt

/--
高さが異なる場合のsafety（k-finalization版）

Coq: `Lemma k_non_equal_height_case`
-/
lemma k_non_equal_height_case :
    ∀ (st : State Validator Hash) (b1 : Hash) (b1_h : ℕ) (b2 : Hash) (b2_h : ℕ) (k1 k2 : ℕ),
      k_finalized hash_parent stake vset st b1 b1_h k1 →
      k_finalized hash_parent stake vset st b2 b2_h k2 →
      ¬ hash_ancestor hash_parent b2 b1 →
      b1_h > b2_h →
      q_intersection_slashed stake vset st := by
  intro st b1 b1_h b2 b2_h k1 k2 Hb1f Hb2f Hx Hh
  have Hb1j := k_finalized_means_justified hash_parent stake vset st b1 b1_h k1 Hb1f
  exact k_non_equal_height_case_ind hash_parent genesis stake vset st
    b1 b1_h b2 b2_h k2 Hb1j Hb2f Hx Hh

/--
高さが等しい場合のsafety

Coq: `Lemma k_equal_height_case`
-/
lemma k_equal_height_case :
    ∀ (st : State Validator Hash) (b1 b2 : Hash) (h : ℕ) (k1 k2 : ℕ),
      k_finalized hash_parent stake vset st b1 h k1 →
      k_finalized hash_parent stake vset st b2 h k2 →
      b1 ≠ b2 →
      q_intersection_slashed stake vset st := by
  intro st b1 b2 h k1 k2 Hf1 Hf2 Hh
  have Hf1' := k_finalized_means_justified hash_parent stake vset st b1 h k1 Hf1
  have Hf2' := k_finalized_means_justified hash_parent stake vset st b2 h k2 Hf2
  by_cases hqs : q_intersection_slashed stake vset st
  · exact hqs
  · have Hconf := no_two_justified_same_height hash_parent stake vset st
      b1 h b2 h Hf1' Hf2' hqs Hh
    contradiction

/--
k-safety補題

Coq: `Lemma k_safety'`
-/
lemma k_safety' :
    ∀ (st : State Validator Hash) (b1 : Hash) (b1_h : ℕ) (b2 : Hash) (b2_h : ℕ) (k1 k2 : ℕ),
      k_finalized hash_parent stake vset st b1 b1_h k1 →
      k_finalized hash_parent stake vset st b2 b2_h k2 →
      ¬ hash_ancestor hash_parent b2 b1 →
      ¬ hash_ancestor hash_parent b1 b2 →
      q_intersection_slashed stake vset st := by
  intro st b1 b1_h b2 b2_h k1 k2 Hf1 Hf2 Hh1 Hh2
  have Hn := hash_nonancestor_nonequal hash_parent b1 b2 Hh2
  by_cases heq : b1_h = b2_h
  · -- 高さが等しい場合
    subst heq
    exact k_equal_height_case hash_parent stake vset st b1 b2 b2_h k1 k2 Hf1 Hf2 Hn
  · -- 高さが異なる場合
    by_cases hgt : b1_h > b2_h
    · exact k_non_equal_height_case hash_parent genesis stake vset st
        b1 b1_h b2 b2_h k1 k2 Hf1 Hf2 Hh1 hgt
    · -- b2_h > b1_hの場合
      have hgt' : b2_h > b1_h := by omega
      exact k_non_equal_height_case hash_parent genesis stake vset st
        b2 b2_h b1 b1_h k2 k1 Hf2 Hf1 Hh2 hgt'

/-!
## メイン定理
-/

/--
k-Accountable Safety定理

Coq: `Theorem k_accountable_safety`

注意: 元のCoqコードでは`Reconstr.hobvious`を使用していますが、
この証明はk_safety'を直接適用すれば証明できます。
-/
theorem k_accountable_safety :
    ∀ (st : State Validator Hash) (k1 k2 : ℕ),
      k_finalization_fork hash_parent stake vset st k1 k2 →
      q_intersection_slashed stake vset st := by
  intro st k1 k2 ⟨b1, b1_h, b2, b2_h, Hf1, Hf2, Hnot1, Hnot2⟩
  exact k_safety' hash_parent genesis stake vset st b1 b1_h b2 b2_h k1 k2
    Hf1 Hf2 Hnot1 Hnot2

/--
Accountable Safety定理（メイン結果）

2つの競合するブロックが両方finalizedされる場合、
少なくとも1/3のstakeを持つquorumがスラッシングされる。

Coq: `Theorem accountable_safety`
-/
theorem accountable_safety :
    ∀ (st : State Validator Hash),
      finalization_fork hash_parent stake vset st →
      q_intersection_slashed stake vset st := by
  intro st Hfin
  have Hfin1 := finalization_fork_means_same_finalization_fork_one hash_parent stake vset st
  have Hfin' := Hfin1.mp Hfin
  exact k_accountable_safety hash_parent genesis stake vset st 1 1 Hfin'

/-
# PlausibleLiveness - Plausible Liveness定理

Coq元ファイル: casper/coq/theories/PlausibleLiveness.v

## 概要
Gasper protocolにおけるPlausible Liveness定理を証明します。
この定理は、2/3のvalidatorが正しく振る舞う限り、
常に新しいブロックをfinalizeできることを保証します。

## 注意事項
- この翻訳では、非常に複雑な構成的証明が含まれています。
- fsetとhighest演算子を扱う証明は、Lean4のFinsetに適応させています。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic
import Casper.NatExt
import Casper.StrongInductionLtn
import Casper.Validator
import Casper.Weight
import Casper.HashTree
import Casper.State
import Casper.Slashing
import Casper.Quorums
import Casper.Justification
import Casper.AccountableSafety

open Classical
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
## 補助的な定義
-/

/--
投票が正当化されたソースを持つ

Coq: `Definition justified_source_votes st v :=
      forall s t s_h t_h,
        vote_msg st v s t s_h t_h -> justified st s s_h.`
-/
def justified_source_votes (st : State Validator Hash) (v : Validator) : Prop :=
  ∀ (s t : Hash) (s_h t_h : ℕ),
    vote_msg st v s t s_h t_h → justified hash_parent stake vset st s s_h

/--
投票が有効な前方リンクを構成する

Coq: `Definition forward_link_votes st v :=
      forall s t s_h t_h,
        vote_msg st v s t s_h t_h ->
        t_h > s_h /\ nth_ancestor (t_h - s_h) s t.`
-/
def forward_link_votes (st : State Validator Hash) (v : Validator) : Prop :=
  ∀ (s t : Hash) (s_h t_h : ℕ),
    vote_msg st v s t s_h t_h →
    t_h > s_h ∧ NthAncestor hash_parent (t_h - s_h) s t

/--
良い投票の定義（2/3 quorumのvalidatorは全て良い投票を行う）

Coq: `Definition good_votes (st : State) :=
      forall b q2, quorum_2 q2 b ->
        forall v, v \in q2 ->
        justified_source_votes st v /\ forward_link_votes st v.`
-/
def good_votes (st : State Validator Hash) : Prop :=
  ∀ (b : Hash) (q2 : Finset Validator),
    quorum_2 stake vset q2 b →
    ∀ v ∈ q2, justified_source_votes hash_parent stake vset st v ∧
              forward_link_votes hash_parent st v

/--
2/3の良いvalidatorが存在する（全てのブロックに対して）

Coq: `Definition two_thirds_good (st : State) :=
      forall b, exists q2, quorum_2 q2 b /\
        forall v, v \in q2 -> ~ slashed st v.`
-/
def two_thirds_good (st : State Validator Hash) : Prop :=
  ∀ (b : Hash), ∃ (q2 : Finset Validator),
    quorum_2 stake vset q2 b ∧
    ∀ v ∈ q2, ¬ slashed st v

/--
指定されたブロックより十分高いブロックが存在する

Coq: `Definition blocks_exist_high_over (base : Hash) : Prop :=
      forall n, exists block, nth_ancestor n base block /\ n > 1.`
-/
def blocks_exist_high_over (base : Hash) : Prop :=
  ∀ (n : ℕ), ∃ (block : Hash), NthAncestor hash_parent n base block ∧ n > 1

/--
最高のjustifiedブロックの性質

Coq: `Definition highest_justified st b b_h : Prop :=
      forall b' b_h', b_h' >= b_h
      -> justified st b' b_h'
      -> b' = b /\ b_h' = b_h.`
-/
def highest_justified (st : State Validator Hash) (b : Hash) (b_h : ℕ) : Prop :=
  ∀ (b' : Hash) (b_h' : ℕ),
    b_h' ≥ b_h →
    justified hash_parent stake vset st b' b_h' →
    b' = b ∧ b_h' = b_h

/--
justification linkが存在する

Coq: `Definition has_justification_link (st : State) : Prop :=
      exists s t s_h t_h, justified st s s_h /\ justification_link st s t s_h t_h.`
-/
def has_justification_link (st : State Validator Hash) : Prop :=
  ∃ (s t : Hash) (s_h t_h : ℕ),
    justified hash_parent stake vset st s s_h ∧
    justification_link hash_parent stake vset st s t s_h t_h

/--
最大のjustification link

Coq: `Definition maximal_justification_link st s t s_h t_h : Prop :=
      justification_link st s t s_h t_h /\
      forall s' t' s_h' t_h', justification_link st s' t' s_h' t_h' -> t_h' <= t_h.`
-/
def maximal_justification_link (st : State Validator Hash) (s t : Hash) (s_h t_h : ℕ) : Prop :=
  justification_link hash_parent stake vset st s t s_h t_h ∧
  ∀ (s' t' : Hash) (s_h' t_h' : ℕ),
    justification_link hash_parent stake vset st s' t' s_h' t_h' → t_h' ≤ t_h

/--
スラッシングされていないvalidatorのみが拡張できる

Coq: `Definition unslashed_can_extend st st' : Prop :=
      forall v s t s_h t_h,
        vote_msg st' v s t s_h t_h = true ->
        vote_msg st v s t s_h t_h = true \/ ~ slashed st v.`
-/
def unslashed_can_extend (st st' : State Validator Hash) : Prop :=
  ∀ (v : Validator) (s t : Hash) (s_h t_h : ℕ),
    vote_msg st' v s t s_h t_h →
    vote_msg st v s t s_h t_h ∨ ¬ slashed st v

/--
新しくスラッシングされるvalidatorがいない

Coq: `Definition no_new_slashed st st' :=
      forall v, slashed st' v -> slashed st v.`
-/
def no_new_slashed (st st' : State Validator Hash) : Prop :=
  ∀ v, slashed st' v → slashed st v

/-!
## 補助的な補題
-/

/--
良い投票はソースが正当化されていることを意味する

Coq: `Lemma good_votes_mean_source_justified`
-/
lemma good_votes_mean_source_justified :
    ∀ (st : State Validator Hash) (s t : Hash) (s_h t_h : ℕ),
      good_votes hash_parent stake vset st →
      justification_link hash_parent stake vset st s t s_h t_h →
      justified hash_parent stake vset st s s_h := by
  intro st s t s_h t_h Hgood Hjlink
  obtain ⟨Hh, Hnth, Hsm⟩ := Hjlink
  specialize Hgood t (link_supporters st s t s_h t_h) Hsm
  obtain ⟨v, hv⟩ := quorum_2_nonempty stake vset t (link_supporters st s t s_h t_h) Hsm
  have ⟨H, _⟩ := Hgood v hv
  unfold link_supporters at hv
  simp [Finset.mem_filter] at hv
  exact H s t s_h t_h hv.2

/--
最大のjustification linkが存在する

Coq: `Lemma maximal_link_exists`

注意: この証明は非常に複雑で、fsetとhighest演算子を多用しています。
-/
lemma maximal_link_exists :
    ∀ (st : State Validator Hash),
      good_votes hash_parent stake vset st →
      has_justification_link hash_parent stake vset st →
      ∃ (s t : Hash) (s_h t_h : ℕ),
        maximal_justification_link hash_parent stake vset st s t s_h t_h := by
  intro st Hgood ⟨s₀, t₀, s₀_h, t₀_h, Hsj₀, Hjl₀⟩
  -- target heightの集合を構築 (supermajority linkを持つ投票のターゲット高さ)
  -- Stateは有限なので、この集合も有限
  haveI : DecidablePred (fun (vote : Vote Validator Hash) =>
    supermajority_link stake vset st (vote_source vote) (vote_target vote)
      (vote_source_height vote) (vote_target_height vote)) := by
    intro vote
    exact Classical.dec _
  let sm_votes := st.filter (fun vote =>
    supermajority_link stake vset st (vote_source vote) (vote_target vote)
      (vote_source_height vote) (vote_target_height vote))
  let target_heights := sm_votes.image (fun vote => vote_target_height vote)
  -- sm_votesが空でないことを示す
  -- Hjl₀より、少なくとも1つのsupermajority linkが存在
  obtain ⟨Hth₀, Hnth₀, Hsm₀⟩ := Hjl₀
  -- supermajority linkを持つvalidatorが存在
  obtain ⟨v₀, hv₀⟩ := quorum_2_nonempty stake vset t₀ (link_supporters st s₀ t₀ s₀_h t₀_h) Hsm₀
  -- v₀の投票がsm_votesに属することを示す
  have hv₀_in_st : (v₀, s₀, t₀, s₀_h, t₀_h) ∈ st := by
    unfold link_supporters at hv₀
    simp [Finset.mem_filter] at hv₀
    exact hv₀.2
  have hv₀_in_sm : (v₀, s₀, t₀, s₀_h, t₀_h) ∈ sm_votes := by
    simp only [sm_votes, Finset.mem_filter]
    constructor
    · exact hv₀_in_st
    · -- supermajority_link st s₀ t₀ s₀_h t₀_h を証明
      simp only [vote_source, vote_target, vote_source_height, vote_target_height]
      exact Hsm₀
  -- target_heightsが空でないことを示す
  have h_ne : target_heights.Nonempty := by
    use t₀_h
    simp only [target_heights, Finset.mem_image]
    use (v₀, s₀, t₀, s₀_h, t₀_h)
    simp [hv₀_in_sm, vote_target_height]
  -- target_heightsの最大値を取得
  obtain ⟨max_th, hmax_th⟩ := Finset.max_of_nonempty h_ne
  have hmax_mem : max_th ∈ target_heights := Finset.max_mem h_ne
  -- max_thに対応する投票を取得
  simp only [target_heights, Finset.mem_image] at hmax_mem
  obtain ⟨max_vote, hmax_vote_in_sm, hmax_eq⟩ := hmax_mem
  simp only [sm_votes, Finset.mem_filter] at hmax_vote_in_sm
  obtain ⟨hmax_vote_in_st, hmax_sm⟩ := hmax_vote_in_sm
  -- 最大の投票に対応するjustification linkを構築
  use vote_source max_vote, vote_target max_vote,
      vote_source_height max_vote, vote_target_height max_vote
  constructor
  · -- justification_linkを証明
    -- good_votesを使用してforward_link_votesを取得
    have Hgood' := Hgood (vote_target max_vote)
      (link_supporters st (vote_source max_vote) (vote_target max_vote)
        (vote_source_height max_vote) (vote_target_height max_vote)) hmax_sm
    -- max_voteのvalidatorがlink_supportersに属する
    have hval_in_ls : vote_val max_vote ∈
        link_supporters st (vote_source max_vote) (vote_target max_vote)
          (vote_source_height max_vote) (vote_target_height max_vote) := by
      unfold link_supporters
      simp [Finset.mem_filter]
      constructor
      · trivial
      · -- vote_msgを証明
        unfold vote_msg
        simp only [vote_val, vote_source, vote_target, vote_source_height, vote_target_height]
        -- max_vote = (v, s, t, s_h, t_h) の形に展開
        rcases max_vote with ⟨v, s, t, s_h, t_h⟩
        exact hmax_vote_in_st
    obtain ⟨_, Hfwd⟩ := Hgood' (vote_val max_vote) hval_in_ls
    unfold forward_link_votes at Hfwd
    rcases max_vote with ⟨v, s, t, s_h, t_h⟩
    simp only [vote_val, vote_source, vote_target, vote_source_height, vote_target_height] at *
    have Hvote_in : vote_msg st v s t s_h t_h := hmax_vote_in_st
    obtain ⟨Hht, Hnth⟩ := Hfwd s t s_h t_h Hvote_in
    exact ⟨Hht, Hnth, hmax_sm⟩
  · -- maximalityを証明
    intro s' t' s_h' t_h' ⟨Hht', Hnth', Hsm'⟩
    -- Hsm'からlink_supportersが空でない
    obtain ⟨v', hv'⟩ := quorum_2_nonempty stake vset t' (link_supporters st s' t' s_h' t_h') Hsm'
    have hv'_in_st : (v', s', t', s_h', t_h') ∈ st := by
      unfold link_supporters at hv'
      simp [Finset.mem_filter] at hv'
      exact hv'.2
    have hv'_in_sm : (v', s', t', s_h', t_h') ∈ sm_votes := by
      simp only [sm_votes, Finset.mem_filter]
      constructor
      · exact hv'_in_st
      · simp only [vote_source, vote_target, vote_source_height, vote_target_height]
        exact Hsm'
    have ht'_in : t_h' ∈ target_heights := by
      simp only [target_heights, Finset.mem_image]
      use (v', s', t', s_h', t_h')
      simp [hv'_in_sm, vote_target_height]
    -- max_thが最大なので t_h' ≤ max_th
    have hle := Finset.le_max_of_mem ht'_in hmax_th
    rw [← hmax_eq]
    exact hle

/--
最大のjustification linkのターゲットは最高のjustifiedブロック

Coq: `Lemma maximal_link_highest_block`
-/
lemma maximal_link_highest_block :
    ∀ (st : State Validator Hash) (s t : Hash) (s_h t_h : ℕ) (b : Hash) (b_h : ℕ),
      ¬ q_intersection_slashed stake vset st →
      good_votes hash_parent stake vset st →
      maximal_justification_link hash_parent stake vset st s t s_h t_h →
      justified hash_parent stake vset st b b_h →
      b_h ≥ t_h →
      b = t ∧ b_h = t_h := by
  intro st s t s_h t_h b b_h Hunslashed Hgood Hmaxjl Hbj Hbh
  obtain ⟨Hjl, Hmaxjl'⟩ := Hmaxjl
  have Hsj := good_votes_mean_source_justified hash_parent stake vset st s t s_h t_h Hgood Hjl
  have Htj := justified.link s s_h t t_h Hsj Hjl
  by_cases heq : b_h = t_h
  · -- b_h = t_hの場合
    subst heq
    constructor
    · by_cases heq_b : b = t
      · exact heq_b
      · have Hsafe := no_two_justified_same_height hash_parent stake vset st
          b t_h t t_h Hbj Htj Hunslashed heq_b
        contradiction
    · rfl
  · -- b_h ≠ t_hの場合
    cases Hbj with
    | genesis =>
        -- bがgenesisの場合、矛盾
        simp at Hbh
        omega
    | link s' s_h' t' t_h' Hjs' Hjl' =>
        -- bがjustification linkの場合
        have h_max := Hmaxjl' s' t' s_h' t_h' Hjl'
        have : t_h' ≤ t_h ∧ t_h ≤ t_h' := ⟨h_max, Hbh⟩
        have : t_h' = t_h := by omega
        contradiction

/--
最高のjustifiedブロックが存在する

Coq: `Lemma highest_exists`
-/
lemma highest_exists :
    ∀ (st : State Validator Hash),
      ¬ q_intersection_slashed stake vset st →
      good_votes hash_parent stake vset st →
      ∃ (b : Hash) (b_h : ℕ),
        justified hash_parent stake vset st b b_h ∧
        highest_justified hash_parent stake vset st b b_h := by
  intro st Hq Hgood
  by_cases hj : has_justification_link hash_parent stake vset st
  · -- justification linkが存在する場合
    obtain ⟨max_s, max_t, max_s_h, max_t_h, Hmax_jlink⟩ :=
      maximal_link_exists hash_parent genesis stake vset st Hgood hj
    use max_t, max_t_h
    obtain ⟨Hmaxj, Hmaximal_link⟩ := Hmax_jlink
    constructor
    · have Hsj := good_votes_mean_source_justified hash_parent stake vset st
        max_s max_t max_s_h max_t_h Hgood Hmaxj
      exact justified.link max_s max_s_h max_t max_t_h Hsj Hmaxj
    · intro b b_h Hbmax Hbj
      exact maximal_link_highest_block hash_parent genesis stake vset st
        max_s max_t max_s_h max_t_h b b_h Hq Hgood Hmax_jlink Hbj Hbmax
  · -- justification linkが存在しない場合、genesisが最高
    use genesis, 0
    constructor
    · exact justified.genesis
    · intro b' b_h' Hb_h' Hb'justified
      push_neg at hj
      cases Hb'justified with
      | genesis => constructor <;> rfl
      | link s b' s_h b_h' Hjs Hjl =>
          exfalso
          apply hj
          use s, b', s_h, b_h'

/-!
## メイン定理
-/

/--
Plausible Liveness定理

2/3のvalidatorが正しく振る舞う限り、
常に新しいブロックをfinalizeできる。

Coq: `Theorem plausible_liveness`

注意: この証明は非常に長く複雑です（約240行）。
新しい投票集合を構成し、それらがスラッシング条件に違反しないことを示します。
-/
theorem plausible_liveness :
    ∀ (st : State Validator Hash),
      two_thirds_good st →
      ¬ q_intersection_slashed stake vset st →
      good_votes hash_parent stake vset st →
      (∀ (b : Hash) (b_h : ℕ),
        highest_justified hash_parent stake vset st b b_h →
        blocks_exist_high_over hash_parent b) →
      ∃ (st' : State Validator Hash),
        unslashed_can_extend st st' ∧
        no_new_slashed st st' ∧
        ∃ (new_finalized new_final_child : Hash) (new_height : ℕ),
          justified hash_parent stake vset st' new_finalized new_height ∧
          hash_parent new_finalized new_final_child ∧
          supermajority_link stake vset st' new_finalized new_final_child
            new_height (new_height + 1) := by
  intro st Hgood Hunslashed Hgood_votes Hheight
  -- 最高のjustifiedブロックを取得
  obtain ⟨just_max, just_max_h, Hjust_max_just, Hjust_max_max⟩ :=
    highest_exists hash_parent genesis stake vset st Hunslashed Hgood_votes
  specialize Hheight just_max just_max_h Hjust_max_max

  -- ターゲット高さの集合を構築
  -- Stateは有限なので、この集合も有限
  let targets : Finset ℕ := ({0} : Finset ℕ) ∪ st.image (fun vote => vote_target_height vote)

  -- highest_targetの計算: targetsの最大値
  -- 0 ∈ targets なので空でない
  have h_ne : targets.Nonempty := by
    use 0
    simp only [targets, Finset.mem_union, Finset.mem_singleton]
    left; rfl

  -- 最大値を取得
  obtain ⟨highest_target, h_highest⟩ := Finset.max_of_nonempty h_ne
  have h_highest_mem : highest_target ∈ targets := Finset.max_mem h_ne

  -- stの全ての投票のターゲット高さはhighest_target以下
  have H_st_highest : ∀ (v' : Validator) (s' t' : Hash) (s_h' t_h' : ℕ),
      (v', s', t', s_h', t_h') ∈ st → t_h' ≤ highest_target := by
    intros v' s' t' s_h' t_h' Hvote
    apply Finset.le_max_of_mem _ h_highest
    simp only [targets, Finset.mem_union, Finset.mem_image]
    right
    use (v', s', t', s_h', t_h')
    simp [Hvote, vote_target_height]

  -- blocks_exist_high_overの仮定を使って、新しいブロックを取得
  -- highest_target + 1より高い位置にあるブロックが必要
  have hdist : (highest_target + 1 - just_max_h) + 1 > 1 := by omega
  obtain ⟨new_final_child, Hpath, _⟩ := Hheight ((highest_target + 1 - just_max_h) + 1)

  -- Hpath : NthAncestor (highest_target + 1 - just_max_h + 1) just_max new_final_child
  -- これをinversionしてnew_finalizedを得る
  cases Hpath with
  | zero =>
      -- 0 = (highest_target + 1 - just_max_h + 1) は矛盾
      omega
  | succ n h1 h2 h3 Hpath_prev Hparent_nf =>
      -- h2 = new_finalized, h3 = new_final_child
      rename_i h_new_finalized
      let new_finalized := h2

      -- 良いquorumを取得
      obtain ⟨good_quorum_f, Hgood_is_quorum_f, Hgood_f⟩ := Hgood new_finalized
      obtain ⟨good_quorum_c, Hgood_is_quorum_c, Hgood_c⟩ := Hgood new_final_child

      -- 新しい投票集合を構築
      let new_votes1 : State Validator Hash :=
        good_quorum_f.image (fun v => (v, just_max, new_finalized, just_max_h, highest_target + 1))
      let new_votes2 : State Validator Hash :=
        good_quorum_c.image (fun v => (v, new_finalized, new_final_child, highest_target + 1, highest_target + 2))

      -- 新しい状態
      let st' : State Validator Hash := st ∪ new_votes1 ∪ new_votes2

      use st'
      constructor

      -- (1) unslashed_can_extend st st'
      · intro v s t s_h t_h Hvote
        simp only [st', new_votes1, new_votes2] at Hvote
        rw [Finset.mem_union, Finset.mem_union] at Hvote
        rcases Hvote with (Hvote | Hvote) | Hvote
        · left; exact Hvote
        · right
          simp [Finset.mem_image] at Hvote
          obtain ⟨x, hx_in, heq⟩ := Hvote
          have : v = x := by simp_all only [Prod.mk.injEq, and_true]
          subst this
          exact Hgood_f x hx_in
        · right
          simp [Finset.mem_image] at Hvote
          obtain ⟨x, hx_in, heq⟩ := Hvote
          have : v = x := by simp_all only [Prod.mk.injEq, and_true]
          subst this
          exact Hgood_c x hx_in

      constructor

      -- (2) no_new_slashed st st'
      · intro badV Hslashed'
        unfold slashed at Hslashed'
        rcases Hslashed' with Hdbl | Hnest

        -- ダブル投票でスラッシュされたケース
        · left
          unfold slashed_double_vote at Hdbl ⊢
          unfold vote_msg at Hdbl ⊢
          obtain ⟨t1, t2, Hneq_t, s1, s1_h, s2, s2_h, t_h, Hvote1, Hvote2⟩ := Hdbl
          use t1, t2, Hneq_t, s1, s1_h, s2, s2_h, t_h

          -- Hvote1の解析
          simp only [st', new_votes1, new_votes2] at Hvote1 Hvote2
          rw [Finset.mem_union, Finset.mem_union] at Hvote1 Hvote2

          -- 両方の投票がstにある場合
          rcases Hvote1 with ((Hvote1_st | Hvote1_nv1) | Hvote1_nv2)
          · have ht_h_le : t_h ≤ highest_target := H_st_highest badV s1 t1 s1_h t_h Hvote1_st
            rcases Hvote2 with ((Hvote2_st | Hvote2_nv1) | Hvote2_nv2)
            · exact ⟨Hvote1_st, Hvote2_st⟩
            · simp [Finset.mem_image] at Hvote2_nv1
              obtain ⟨_, _, heq⟩ := Hvote2_nv1
              simp only [Prod.mk.injEq] at heq
              obtain ⟨_, _, _, _, ht_h_eq⟩ := heq
              omega
            · simp [Finset.mem_image] at Hvote2_nv2
              obtain ⟨_, _, heq⟩ := Hvote2_nv2
              simp only [Prod.mk.injEq] at heq
              obtain ⟨_, _, _, _, ht_h_eq⟩ := heq
              omega
          · rcases Hvote2 with ((Hvote2_st | Hvote2_nv1) | Hvote2_nv2)
            · simp [Finset.mem_image] at Hvote1_nv1
              obtain ⟨_, _, heq1⟩ := Hvote1_nv1
              simp only [Prod.mk.injEq] at heq1
              obtain ⟨_, _, _, _, ht_h_eq1⟩ := heq1
              have ht_h_le : t_h ≤ highest_target := H_st_highest badV s2 t2 s2_h t_h Hvote2_st
              omega
            · simp [Finset.mem_image] at Hvote1_nv1 Hvote2_nv1
              obtain ⟨_, _, heq1⟩ := Hvote1_nv1
              obtain ⟨_, _, heq2⟩ := Hvote2_nv1
              simp only [Prod.mk.injEq] at heq1 heq2
              obtain ⟨_, _, ht1_eq, _, _⟩ := heq1
              obtain ⟨_, _, ht2_eq, _, _⟩ := heq2
              rw [ht1_eq, ht2_eq] at Hneq_t
              exact absurd rfl Hneq_t
            · simp [Finset.mem_image] at Hvote1_nv1 Hvote2_nv2
              obtain ⟨_, _, heq1⟩ := Hvote1_nv1
              obtain ⟨_, _, heq2⟩ := Hvote2_nv2
              simp only [Prod.mk.injEq] at heq1 heq2
              obtain ⟨_, _, _, _, ht_h_eq1⟩ := heq1
              obtain ⟨_, _, _, _, ht_h_eq2⟩ := heq2
              omega
          · rcases Hvote2 with ((Hvote2_st | Hvote2_nv1) | Hvote2_nv2)
            · simp [Finset.mem_image] at Hvote1_nv2
              obtain ⟨_, _, heq1⟩ := Hvote1_nv2
              simp only [Prod.mk.injEq] at heq1
              obtain ⟨_, _, _, _, ht_h_eq1⟩ := heq1
              have ht_h_le : t_h ≤ highest_target := H_st_highest badV s2 t2 s2_h t_h Hvote2_st
              omega
            · simp [Finset.mem_image] at Hvote1_nv2 Hvote2_nv1
              obtain ⟨_, _, heq1⟩ := Hvote1_nv2
              obtain ⟨_, _, heq2⟩ := Hvote2_nv1
              simp only [Prod.mk.injEq] at heq1 heq2
              obtain ⟨_, _, _, _, ht_h_eq1⟩ := heq1
              obtain ⟨_, _, _, _, ht_h_eq2⟩ := heq2
              omega
            · simp [Finset.mem_image] at Hvote1_nv2 Hvote2_nv2
              obtain ⟨_, _, heq1⟩ := Hvote1_nv2
              obtain ⟨_, _, heq2⟩ := Hvote2_nv2
              simp only [Prod.mk.injEq] at heq1 heq2
              obtain ⟨_, _, ht1_eq, _, _⟩ := heq1
              obtain ⟨_, _, ht2_eq, _, _⟩ := heq2
              rw [ht1_eq, ht2_eq] at Hneq_t
              exact absurd rfl Hneq_t

        -- サラウンド投票でスラッシュされたケース
        · right
          unfold slashed_surround_vote at Hnest ⊢
          unfold vote_msg at Hnest ⊢
          obtain ⟨s1, t1, s1_h, t1_h, s2, t2, s2_h, t2_h, Houter, Hinner, Hstarts, Hends⟩ := Hnest
          use s1, t1, s1_h, t1_h, s2, t2, s2_h, t2_h

          simp only [st', new_votes1, new_votes2] at Houter Hinner
          rw [Finset.mem_union, Finset.mem_union] at Houter Hinner

          -- justifiedブロックの高さはhighest_target以下
          have Hjust_le_target : ∀ (n : Hash) (n_h : ℕ),
              justified hash_parent stake vset st n n_h → n_h ≤ highest_target := by
            intro n n_h Hjn
            cases Hjn with
            | genesis =>
                apply Finset.le_max_of_mem _ h_highest
                simp only [targets, Finset.mem_union, Finset.mem_singleton]
                left; rfl
            | link s_j s_j_h t_j t_j_h Hjs Hjl =>
                obtain ⟨_, _, Hsm_jl⟩ := Hjl
                unfold supermajority_link link_supporters at Hsm_jl
                obtain ⟨v_j, hv_j⟩ := quorum_2_nonempty stake vset t_j
                  (Finset.univ.filter fun v => vote_msg st v s_j t_j s_j_h t_j_h) Hsm_jl
                simp [Finset.mem_filter] at hv_j
                have h_vote_in : (v_j, s_j, t_j, s_j_h, t_j_h) ∈ st := hv_j.2
                apply Finset.le_max_of_mem _ h_highest
                simp only [targets, Finset.mem_union, Finset.mem_image]
                right
                use (v_j, s_j, t_j, s_j_h, t_j_h)
                simp [h_vote_in, vote_target_height]

          -- 外側の投票を解析
          rcases Houter with ((Houter_st | Houter_nv1) | Houter_nv2)
          · have ht1_h_le : t1_h ≤ highest_target := H_st_highest badV s1 t1 s1_h t1_h Houter_st
            rcases Hinner with ((Hinner_st | Hinner_nv1) | Hinner_nv2)
            · exact ⟨⟨Houter_st, Hinner_st⟩, Hstarts, Hends⟩
            · simp [Finset.mem_image] at Hinner_nv1
              obtain ⟨_, _, heq⟩ := Hinner_nv1
              simp only [Prod.mk.injEq] at heq
              obtain ⟨_, _, _, _, ht2_h_eq⟩ := heq
              -- t2_h = highest_target + 1, だが t1_h ≤ highest_target かつ t2_h < t1_h
              omega
            · simp [Finset.mem_image] at Hinner_nv2
              obtain ⟨_, _, heq⟩ := Hinner_nv2
              simp only [Prod.mk.injEq] at heq
              obtain ⟨_, _, _, _, ht2_h_eq⟩ := heq
              omega

          · simp [Finset.mem_image] at Houter_nv1
            obtain ⟨x_outer, hx_outer_in, heq_outer⟩ := Houter_nv1
            simp only [Prod.mk.injEq] at heq_outer
            obtain ⟨_, hs1_eq, ht1_eq, hs1_h_eq, ht1_h_eq⟩ := heq_outer

            rcases Hinner with ((Hinner_st | Hinner_nv1) | Hinner_nv2)
            · -- 内側の投票がstにある
              -- badVはgood_quorum_fのメンバー (Houter_nv1から)
              -- good_quorum_fのメンバーはスラッシュされていない
              have Hnot_slashed := Hgood_f badV (by rw [← heq_outer.1]; exact hx_outer_in)
              -- good_votesより、badVの投票はjustifiedなソースを持つ
              have HgoodbadV := Hgood_votes new_finalized good_quorum_f Hgood_is_quorum_f badV
                (by rw [← heq_outer.1]; exact hx_outer_in)
              obtain ⟨Hjsv, _⟩ := HgoodbadV
              unfold justified_source_votes at Hjsv
              have Hs2_just := Hjsv s2 t2 s2_h t2_h Hinner_st
              have Hs2_h_le := Hjust_le_target s2 s2_h Hs2_just
              -- s1_h = just_max_h で s2_h < s1_h = just_max_h
              -- しかし、Hjust_max_maxより、s2_h ≥ just_max_h ならば s2 = just_max かつ s2_h = just_max_h
              -- s2_h < s1_h = just_max_h なので矛盾しない限り...
              rw [hs1_h_eq] at Hstarts
              have Hs2_just' := Hjust_le_target s2 s2_h Hs2_just
              -- Hjust_max_maxを使う
              by_cases h_s2_ge : s2_h ≥ just_max_h
              · have ⟨_, hs2_h_eq⟩ := Hjust_max_max s2 s2_h h_s2_ge Hs2_just
                rw [hs2_h_eq] at Hstarts
                omega
              · push_neg at h_s2_ge
                have h_s2_lt : s2_h < just_max_h := h_s2_ge
                -- t2_h < t1_h = highest_target + 1 なので t2_h ≤ highest_target
                rw [ht1_h_eq] at Hends
                have ht2_h_le : t2_h ≤ highest_target := by omega
                -- しかし、s2_h < just_max_h ≤ highest_target かつ t2_h > s2_h
                -- これは stの投票なので t2_h ≤ highest_target も成立
                exact ⟨⟨Houter_st, Hinner_st⟩, Hstarts, Hends⟩

            · simp [Finset.mem_image] at Hinner_nv1
              obtain ⟨_, _, heq_inner⟩ := Hinner_nv1
              simp only [Prod.mk.injEq] at heq_inner
              obtain ⟨_, _, _, hs2_h_eq, ht2_h_eq⟩ := heq_inner
              -- s1_h = just_max_h, s2_h = just_max_h なので s2_h < s1_h は矛盾
              rw [hs1_h_eq, hs2_h_eq] at Hstarts
              omega

            · simp [Finset.mem_image] at Hinner_nv2
              obtain ⟨_, _, heq_inner⟩ := Hinner_nv2
              simp only [Prod.mk.injEq] at heq_inner
              obtain ⟨_, _, _, hs2_h_eq, ht2_h_eq⟩ := heq_inner
              -- t1_h = highest_target + 1, t2_h = highest_target + 2 なので t2_h < t1_h は矛盾
              rw [ht1_h_eq, ht2_h_eq] at Hends
              omega

          · simp [Finset.mem_image] at Houter_nv2
            obtain ⟨x_outer, hx_outer_in, heq_outer⟩ := Houter_nv2
            simp only [Prod.mk.injEq] at heq_outer
            obtain ⟨_, hs1_eq, ht1_eq, hs1_h_eq, ht1_h_eq⟩ := heq_outer

            rcases Hinner with ((Hinner_st | Hinner_nv1) | Hinner_nv2)
            · -- 内側の投票がstにある
              have HgoodbadV := Hgood_votes new_final_child good_quorum_c Hgood_is_quorum_c badV
                (by rw [← heq_outer.1]; exact hx_outer_in)
              obtain ⟨Hjsv, _⟩ := HgoodbadV
              unfold justified_source_votes at Hjsv
              have Hs2_just := Hjsv s2 t2 s2_h t2_h Hinner_st
              have Hs2_h_le := Hjust_le_target s2 s2_h Hs2_just
              rw [hs1_h_eq] at Hstarts
              -- s2_h < s1_h = highest_target + 1 かつ s2_h ≤ highest_target より矛盾ではない
              -- ただし t2_h < t1_h = highest_target + 2 なので t2_h ≤ highest_target + 1
              -- s2_h ≤ highest_target < highest_target + 1 = s1_h より s2_h < s1_h 成立
              have ht2_h_le : t2_h ≤ highest_target := H_st_highest badV s2 t2 s2_h t2_h Hinner_st
              rw [ht1_h_eq] at Hends
              omega

            · simp [Finset.mem_image] at Hinner_nv1
              obtain ⟨_, _, heq_inner⟩ := Hinner_nv1
              simp only [Prod.mk.injEq] at heq_inner
              obtain ⟨_, _, _, hs2_h_eq, _⟩ := heq_inner
              -- just_max_hはjustified、その高さはhighest_target以下
              have Hjmh_le := Hjust_le_target just_max just_max_h Hjust_max_just
              rw [hs1_h_eq, hs2_h_eq] at Hstarts
              omega

            · simp [Finset.mem_image] at Hinner_nv2
              obtain ⟨_, _, heq_inner⟩ := Hinner_nv2
              simp only [Prod.mk.injEq] at heq_inner
              obtain ⟨_, _, _, hs2_h_eq, _⟩ := heq_inner
              rw [hs1_h_eq, hs2_h_eq] at Hstarts
              omega

      -- (3) 新しいfinalizedブロックの存在
      · use new_finalized, new_final_child, (highest_target + 1)
        constructor

        -- new_finalizedがjustified
        · apply justified.link just_max just_max_h new_finalized (highest_target + 1)
          · -- Hjust_max_justをst'に弱める
            apply justified_weaken stake vset st st'
            · intro v hv
              simp only [st', new_votes1, new_votes2]
              rw [Finset.mem_union, Finset.mem_union]
              left; left; exact hv
            · exact Hjust_max_just
          · -- justification_link st' just_max new_finalized just_max_h (highest_target + 1)
            constructor
            · -- highest_target + 1 > just_max_h
              have h0_le : 0 ≤ highest_target := by
                apply Finset.le_max_of_mem _ h_highest
                simp only [targets, Finset.mem_union, Finset.mem_singleton]
                left; rfl
              have Hjmh_le := by
                apply Finset.le_max_of_mem _ h_highest
                simp only [targets, Finset.mem_union, Finset.mem_singleton]
                -- genesisは高さ0でjustified
                cases Hjust_max_just with
                | genesis => left; rfl
                | link s_j s_j_h t_j t_j_h Hjs Hjl =>
                    obtain ⟨_, _, Hsm_jl⟩ := Hjl
                    unfold supermajority_link link_supporters at Hsm_jl
                    obtain ⟨v_j, hv_j⟩ := quorum_2_nonempty stake vset t_j
                      (Finset.univ.filter fun v => vote_msg st v s_j t_j s_j_h t_j_h) Hsm_jl
                    simp [Finset.mem_filter] at hv_j
                    right
                    use (v_j, s_j, t_j, s_j_h, t_j_h)
                    simp [hv_j.2, vote_target_height]
              omega
            constructor
            · -- NthAncestor (highest_target + 1 - just_max_h) just_max new_finalized
              have h_eq : n = highest_target + 1 - just_max_h := by
                -- n + 1 = highest_target + 1 - just_max_h + 1
                -- から n = highest_target + 1 - just_max_h
                -- Hpath_prev : NthAncestor n just_max new_finalized
                -- もとの Hpath は NthAncestor (n + 1) just_max new_final_child
                -- n + 1 = (highest_target + 1 - just_max_h) + 1
                omega
              rw [← h_eq]
              exact Hpath_prev
            · -- supermajority_link st' just_max new_finalized just_max_h (highest_target + 1)
              unfold supermajority_link
              apply quorum_2_upclosed stake vset (highest_target + 1) good_quorum_f
              · -- good_quorum_f ⊆ link_supporters st' just_max new_finalized just_max_h (highest_target + 1)
                intro v hv
                unfold link_supporters
                simp [Finset.mem_filter, vote_msg]
                constructor
                · trivial
                · simp only [st', new_votes1, new_votes2]
                  rw [Finset.mem_union, Finset.mem_union]
                  left; right
                  simp [Finset.mem_image]
                  use v
              · -- link_supporters st' ... ⊆ vset (highest_target + 1)
                intro v hv
                unfold link_supporters at hv
                simp [Finset.mem_filter, vote_msg] at hv
                exact votes_from_target_vset vset v st' just_max just_max_h new_finalized
                  (highest_target + 1) hv.2
              · exact Hgood_is_quorum_f

        constructor
        -- new_finalized <~ new_final_child
        · exact Hparent_nf

        -- supermajority_link st' new_finalized new_final_child (highest_target + 1) (highest_target + 2)
        · unfold supermajority_link
          apply quorum_2_upclosed stake vset (highest_target + 2) good_quorum_c
          · intro v hv
            unfold link_supporters
            simp [Finset.mem_filter, vote_msg]
            constructor
            · trivial
            · simp only [st', new_votes1, new_votes2]
              rw [Finset.mem_union, Finset.mem_union]
              right
              simp [Finset.mem_image]
              use v
          · intro v hv
            unfold link_supporters at hv
            simp [Finset.mem_filter, vote_msg] at hv
            exact votes_from_target_vset vset v st' new_finalized (highest_target + 1)
              new_final_child (highest_target + 2) hv.2
          · exact Hgood_is_quorum_c

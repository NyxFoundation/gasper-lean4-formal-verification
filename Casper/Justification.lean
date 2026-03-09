/-
# Justification - Justificationとfinalizationの定義と性質

Coq元ファイル: casper/coq/theories/Justification.v

## 概要
Casper FFGにおけるjustificationとfinalizationの定義、およびそれらの性質を定義します。

## 注意: カスタムタクティク spec について
元のCoqコードでは、カスタムタクティク `spec` が定義されていますが、
Lean4では各使用箇所で手動展開しています。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Casper.NatExt
import Casper.Validator
import Casper.Weight
import Casper.HashTree
import Casper.State
import Casper.Slashing
import Casper.Quorums

open Casper.NatExt
open Finset

variable {Validator Hash : Type}
variable [Fintype Validator] [DecidableEq Validator]
variable [Fintype Hash] [DecidableEq Hash]
variable (stake : Validator → ℕ)
variable (vset : Hash → Finset Validator)

/-!
## Justificationとfinalizationの定義
-/

/--
特定のリンクに投票したvalidatorの集合

Coq: `Definition link_supporters st s t s_h t_h : {set Validator} :=
       [set v | vote_msg st v s t s_h t_h ].`
-/
def link_supporters (st : State Validator Hash) (s t : Hash) (s_h t_h : ℕ) :
    Finset Validator :=
  Finset.univ.filter (fun v => vote_msg st v s t s_h t_h)

/--
投票は投票対象のターゲットブロックのvsetからのみ発信されるという仮定（Liveness証明に必要）

Coq: `Axiom votes_from_target_vset: forall x st s s_h t t_h,
       x \in link_supporters st s t s_h t_h -> x \in vset.[vs_fun t].`
-/
axiom votes_from_target_vset :
  ∀ (x : Validator) (st : State Validator Hash) (s : Hash) (s_h : ℕ) (t : Hash) (t_h : ℕ),
    x ∈ link_supporters st s t s_h t_h → x ∈ vset t

/--
リンクに対する投票者集合がsupermajorityを構成する

Coq: `Definition supermajority_link (st:State) (s t : Hash) (s_h t_h : nat) : bool :=
       quorum_2 (link_supporters st s t s_h t_h) t.`
-/
def supermajority_link (st : State Validator Hash) (s t : Hash) (s_h t_h : ℕ) : Prop :=
  quorum_2 stake vset (link_supporters st s t s_h t_h) t

/-!
### Supermajority linkの性質
-/

/--
状態に（同じvalidatorからの）投票を追加してもsupermajority linkは保存される

注意: この証明には、追加の投票がvset.[target]から来ている必要があります。

Coq: `Lemma supermajority_weaken: forall (st st':State) s t s_h t_h
       (HSub:forall (v: Vote), v \in st -> v \in st'),
         supermajority_link st s t s_h t_h
         -> supermajority_link st' s t s_h t_h.`
-/
lemma supermajority_weaken :
    ∀ (st st' : State Validator Hash) (s t : Hash) (s_h t_h : ℕ)
      (HSub : ∀ (v : Vote Validator Hash), v ∈ st → v ∈ st'),
      supermajority_link stake vset st s t s_h t_h →
      supermajority_link stake vset st' s t s_h t_h := by
  intro st st' s t s_h t_h Hsub Hsm
  unfold supermajority_link link_supporters at *
  apply quorum_2_upclosed
  · -- link_supporters st ⊆ link_supporters st'
    intro v hv
    simp [Finset.mem_filter] at *
    obtain ⟨_, hvote⟩ := hv
    constructor
    · trivial
    · exact Hsub (v, s, t, s_h, t_h) hvote
  · -- link_supporters st' ⊆ vset t
    intro v hv
    simp [Finset.mem_filter] at hv
    exact votes_from_target_vset vset v st' s s_h t t_h hv.2
  · exact Hsm

/--
Justification linkは正当なリンクでなければならない

Supermajority linkであることに加えて、justification linkは
ブロックツリー内の有効な前方リンクであり、
ターゲットの高さがソースの高さより大きくなければならない。

Coq: `Definition justification_link (st:State) (s t : Hash) (s_h t_h : nat) : Prop :=
       t_h > s_h /\
       nth_ancestor (t_h - s_h) s t /\
       supermajority_link st s t s_h t_h.`
-/
def justification_link (st : State Validator Hash) (s t : Hash) (s_h t_h : ℕ) : Prop :=
  t_h > s_h ∧
  nth_ancestor (t_h - s_h) s t ∧
  supermajority_link stake vset st s t s_h t_h

/-!
### Justificationの帰納的定義
-/

/--
ブロックのjustificationを、genesisブロックからそのブロックまでのパスとして帰納的に定義

Coq: `Inductive justified (st:State) : Hash -> nat -> Prop :=
      | justified_genesis : justified st genesis 0
      | justified_link : forall s s_h t t_h,
          justified st s s_h ->
          justification_link st s t s_h t_h ->
          justified st t t_h.`
-/
inductive justified (st : State Validator Hash) : Hash → ℕ → Prop where
  | genesis : justified st genesis 0
  | link : ∀ (s : Hash) (s_h : ℕ) (t : Hash) (t_h : ℕ),
      justified st s s_h →
      justification_link stake vset st s t s_h t_h →
      justified st t t_h

/--
Justificationは、新しい投票で状態を拡張しても保存される
（justifiedブロックのv-setからの投票）

Coq: `Lemma justified_weaken: forall (st st':State) t t_h
       (HSub:forall (v: Vote), v \in st -> v \in st'),
       justified st t t_h -> justified st' t t_h.`
-/
lemma justified_weaken :
    ∀ (st st' : State Validator Hash) (t : Hash) (t_h : ℕ)
      (HSub : ∀ (v : Vote Validator Hash), v ∈ st → v ∈ st'),
      justified stake vset st t t_h → justified stake vset st' t t_h := by
  intro st st' t t_h Hsub Hjust
  induction Hjust with
  | genesis =>
      apply justified.genesis
  | link s s_h t t_h Hjust_s Hjl ih =>
      obtain ⟨Hh, Ha, Hsm⟩ := Hjl
      apply justified.link
      · exact ih
      · constructor
        · exact Hh
        · constructor
          · exact Ha
          · exact supermajority_weaken stake vset st st' s t s_h t_h Hsub Hsm

/-!
### Finalizationの定義
-/

/--
Finalizedブロックは、justifiedブロックであり、
そのブロックへのsupermajority linkで結ばれた子ブロックもjustifiedである

Coq: `Definition finalized st b b_h :=
       justified st b b_h /\
       exists c, (b <~ c /\ supermajority_link st b c b_h b_h.+1).`
-/
def finalized (st : State Validator Hash) (b : Hash) (b_h : ℕ) : Prop :=
  justified stake vset st b b_h ∧
  ∃ c, (hash_parent b c ∧ supermajority_link stake vset st b c b_h (b_h + 1))

/--
k-finalizedブロックは、justifiedブロックであり、
そのブロックへのsupermajority linkで結ばれたk-子孫もjustifiedであり、
子孫までのすべてのブロックもjustifiedである

Coq: `Definition k_finalized st b b_h k :=
       k >= 1 /\
       exists ls, size ls = k.+1 /\
             head b ls = b /\
             (forall n, n <= k ->
                   justified st (nth b ls n) (b_h+n) /\
                   nth_ancestor n b (nth b ls n)
             ) /\
             supermajority_link st b (last b ls) b_h (b_h+k).`
-/
def k_finalized (st : State Validator Hash) (b : Hash) (b_h : ℕ) (k : ℕ) : Prop :=
  k ≥ 1 ∧
  ∃ ls : List Hash,
    ls.length = k + 1 ∧
    ls.head? = some b ∧
    (∀ n, n ≤ k →
      justified stake vset st (ls.getD n b) (b_h + n) ∧
      nth_ancestor n b (ls.getD n b)) ∧
    supermajority_link stake vset st b (ls.getLast?.getD b) b_h (b_h + k)

/-!
### Finalizationの性質
-/

/--
finalized <-> 1-finalized

Coq: `Lemma finalized_means_one_finalized : forall st b b_h,
       finalized st b b_h <-> k_finalized st b b_h 1.`
-/
lemma finalized_means_one_finalized :
    ∀ (st : State Validator Hash) (b : Hash) (b_h : ℕ),
      finalized stake vset st b b_h ↔ k_finalized stake vset st b b_h 1 := by
  intro st b b_h
  constructor
  -- finalized → k_finalized 1
  · intro ⟨Hjust, c, Hparent, Hsm⟩
    constructor
    · omega  -- 1 ≥ 1
    · use [b, c]
      constructor
      · simp  -- length = 2 = 1 + 1
      · constructor
        · rfl  -- head? = some b
        · constructor
          · intro n Hn
            -- n ≤ 1 なので n = 0 または n = 1
            interval_cases n
            · -- n = 0 の場合
              simp
              constructor
              · exact Hjust
              · exact NthAncestor.zero b
            · -- n = 1 の場合
              simp
              constructor
              · -- c が justified であることを証明
                apply justified.link b b_h c (b_h + 1) Hjust
                exact ⟨Nat.add_comm b_h 1 ▸ (Nat.add_sub_cancel b_h 1 ▸ le_refl _), Hparent, Hsm⟩
              · -- NthAncestor 1 b c を証明
                constructor
                exact NthAncestor.zero b
                exact Hparent
          · simp
            exact Hsm
  -- k_finalized 1 → finalized
  · intro ⟨Hk, ls, Hsize, Hhd, Hrel, Hlink⟩
    constructor
    · -- justified st b b_h を証明
      have h0 := Hrel 0 (Nat.zero_le 1)
      obtain ⟨Hjust, _⟩ := h0
      cases ls with
      | nil => simp at Hsize
      | cons hd tl =>
          simp at Hhd
          simp [List.getD, Hhd, Nat.add_zero] at Hjust
          exact Hjust
    · -- ∃ c を証明
      have h1 := Hrel 1 le_refl
      obtain ⟨Hjust_c, Hanc⟩ := h1
      -- ls の長さは 2 なので、ls = [b, c] の形
      cases ls with
      | nil => simp at Hsize
      | cons hd tl =>
          cases tl with
          | nil => simp at Hsize
          | cons c tl2 =>
              simp at Hsize Hhd Hlink
              -- c を取得
              use c
              constructor
              · -- b <~ c を証明
                have : NthAncestor hash_parent 1 b c := by
                  rw [← Hhd] at Hanc
                  simp [List.getD] at Hanc
                  exact Hanc
                cases this with
                | succ n h1 h2 h3 h_anc h_parent =>
                    have : h1 = h2 := by
                      cases h_anc
                      rfl
                    rw [this]
                    exact h_parent
              · -- supermajority_link st b c b_h (b_h + 1) を証明
                rw [← Hhd] at Hlink
                simp [List.getLast?, List.getD] at Hlink
                exact Hlink

/--
k-finalizedブロックはjustifiedである

Coq: `Lemma k_finalized_means_justified: forall st b b_h k,
       k_finalized st b b_h k -> justified st b b_h.`
-/
lemma k_finalized_means_justified :
    ∀ (st : State Validator Hash) (b : Hash) (b_h : ℕ) (k : ℕ),
      k_finalized stake vset st b b_h k →
      justified stake vset st b b_h := by
  intro st b b_h k ⟨Hk, ls, Hsize, Hhd, Hrel, Hlink⟩
  -- n = 0を適用
  have h0 := Hrel 0 (Nat.zero_le k)
  obtain ⟨Hjust, _⟩ := h0
  -- ls.head? = some b より、ls.getD 0 b = b
  have hb : ls.getD 0 b = b := by
    cases ls with
    | nil => simp at Hsize
    | cons hd tl =>
        simp at Hhd
        simp [List.getD, Hhd]
  -- b_h + 0 = b_h
  have hbh : b_h + 0 = b_h := Nat.add_zero b_h
  rw [hb, hbh] at Hjust
  exact Hjust

/--
Finalizedブロックには、justifiedな子ブロックが存在する

Coq: `Lemma finalized_means_justified_child: forall st p p_h,
       finalized st p p_h -> exists c, p <~ c /\ justified st c p_h.+1.`
-/
lemma finalized_means_justified_child :
    ∀ (st : State Validator Hash) (p : Hash) (p_h : ℕ),
      finalized stake vset st p p_h →
      ∃ c, hash_parent p c ∧ justified stake vset st c (p_h + 1) := by
  intro st p p_h Hfin
  obtain ⟨Hjustified_p, c, Hc_parent, Hc_sm⟩ := Hfin
  use c
  constructor
  · exact Hc_parent
  · have Hp := parent_ancestor p c
    have Hpc := Hp.mp Hc_parent
    have Hc_h : p_h + 1 > p_h := Nat.lt_succ_self p_h
    have Hjl : justification_link stake vset st p c p_h (p_h + 1) := by
      constructor
      · exact Hc_h
      · constructor
        · -- (p_h + 1) - p_h = 1
          have : (p_h + 1) - p_h = 1 := by omega
          rw [this]
          exact Hpc
        · exact Hc_sm
    exact justified.link p p_h c (p_h + 1) Hjustified_p Hjl

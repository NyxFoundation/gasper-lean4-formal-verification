/-
# Quorums - Validator集合、quorum、quorum性質

Coq元ファイル: casper/coq/theories/Quorums.v

## 概要
Validator集合、quorum述語、およびquorum性質を定義します。
Gasper protocolにおけるquorumの概念は、2/3以上のstakeを持つvalidator集合として定義されます。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Casper.NatExt
import Casper.Validator
import Casper.Weight
import Casper.HashTree
import Casper.State
import Casper.Slashing

open Casper.NatExt
open Finset

variable {Validator Hash : Type}
variable [Fintype Validator] [DecidableEq Validator]
variable [Fintype Hash] [DecidableEq Hash]
variable (stake : Validator → ℕ)

/-!
## Validator集合の定義

ブロック毎にvalidator集合を定義する有限マップ。
Coqでは `{fmap Hash -> {set Validator}}` として定義されていますが、
Lean4では単純な関数として表現します。

Coq: `Parameter vset : {fmap Hash -> {set Validator}}.`
Coq: `Axiom vs_fun : forall h : Hash, h \in vset.`
-/

/--
ブロック毎のvalidator集合を定義する関数
Coqのvsetと vs_fun axiomに対応。関数として定義することで自動的にtotalになります。
-/
variable (vset : Hash → Finset Validator)

/-!
## Quorum述語

Casper FFGでは、2つの重要なquorum述語を定義します：
1. quorum_1: 少なくとも1/3の重みを持つvalidator集合
2. quorum_2: 少なくとも2/3の重みを持つvalidator集合（supermajority）
-/

/--
「少なくとも1/3の重み」を持つvalidator集合の述語

Coq: `Definition quorum_1 (vs : {set Validator}) (b : Hash) : bool :=
       (vs \subset vset.[vs_fun b]) &&
       (wt vs >= one_third (wt vset.[vs_fun b])).`
-/
def quorum_1 (vs : Finset Validator) (b : Hash) : Prop :=
  vs ⊆ vset b ∧ wt stake vs ≥ one_third (wt stake (vset b))

/--
「少なくとも2/3の重み」を持つvalidator集合の述語（supermajority）

Coq: `Definition quorum_2 (vs : {set Validator}) (b : Hash) : bool :=
       (vs \subset vset.[vs_fun b]) &&
       (wt vs >= two_third (wt vset.[vs_fun b])).`
-/
def quorum_2 (vs : Finset Validator) (b : Hash) : Prop :=
  vs ⊆ vset b ∧ wt stake vs ≥ two_third (wt stake (vset b))

/-!
## 動的validator集合におけるスラッシング

動的validator集合の一般的なコンテキストにおいて、validator集合がスラッシングされる意味を定義します。
-/

/--
2つのquorum_2の交わりがすべてスラッシングされている状態

Coq: `Definition q_intersection_slashed st :=
       exists (bL bR: Hash) (vL vR: {set Validator}),
         vL \subset vset.[vs_fun bL] /\
         vR \subset vset.[vs_fun bR] /\
         quorum_2 vL bL /\
         quorum_2 vR bR /\
         forall v, v \in vL -> v \in vR -> slashed st v.`
-/
def q_intersection_slashed (st : State Validator Hash) : Prop :=
  ∃ (bL bR : Hash) (vL vR : Finset Validator),
    vL ⊆ vset bL ∧
    vR ⊆ vset bR ∧
    quorum_2 stake vset vL bL ∧
    quorum_2 stake vset vR bR ∧
    ∀ v, v ∈ vL → v ∈ vR → slashed st v

/-!
## Quorumの性質
-/

/--
Supermajority quorumは空でない（Liveness証明に必要）

Coq: `Axiom quorum_2_nonempty:
       forall (b:Hash) (q :{set Validator}),
         quorum_2 q b -> exists v, v \in q.`
-/
axiom quorum_2_nonempty :
  ∀ (b : Hash) (q : Finset Validator),
    quorum_2 stake vset q b → ∃ v, v ∈ q

/--
Supermajority quorumは上方閉包的（Liveness証明に必要）

ブロックbに関して、supermajorityに更にb-validatorを追加しても、
supermajorityのままである。

Coq: `Lemma quorum_2_upclosed:
       forall (b:Hash) (q q':{set Validator}),
         q \subset q' -> q' \subset vset.[vs_fun b] -> quorum_2 q b ->
         quorum_2 q' b.`
-/
lemma quorum_2_upclosed :
    ∀ (b : Hash) (q q' : Finset Validator),
      q ⊆ q' → q' ⊆ vset b → quorum_2 stake vset q b →
      quorum_2 stake vset q' b := by
  intro b q q' Hqsubq' Hq' Hq2
  unfold quorum_2 at *
  obtain ⟨Hq, Hqwt⟩ := Hq2
  constructor
  · exact Hq'
  · have h_wt_inc := wt_inc_leq stake q q' Hqsubq'
    exact Nat.le_trans Hqwt h_wt_inc

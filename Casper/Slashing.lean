/-
# Slashing - スラッシング条件の定義

Coq元ファイル: casper/coq/theories/Slashing.v

## 概要
スラッシング条件（二重投票とサラウンド投票）の定義を提供します。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Casper.Validator
import Casper.HashTree
import Casper.State

variable {Validator Hash : Type}
variable [Fintype Validator] [DecidableEq Validator]
variable [Fintype Hash] [DecidableEq Hash]

/-!
## スラッシング条件

Casper FFGでは、2つのスラッシング条件が定義されています：
1. 二重投票（double vote）
2. サラウンド投票（surround vote）
-/

/-- 二重投票によるスラッシング

validatorは、同じターゲット高さで異なるターゲットハッシュを持つ
2つの投票を行ってはならない（ソースブロックに関係なく）。

Coq: `Definition slashed_double_vote st v := exists t1 t2, t1 <> t2 /\
       exists s1 s1_h s2 s2_h t_h, vote_msg st v s1 t1 s1_h t_h /\ vote_msg st v s2 t2 s2_h t_h.`
-/
def slashed_double_vote (st : State Validator Hash) (v : Validator) : Prop :=
  ∃ (t1 t2 : Hash), t1 ≠ t2 ∧
    ∃ (s1 : Hash) (s1_h : ℕ) (s2 : Hash) (s2_h : ℕ) (t_h : ℕ),
      vote_msg st v s1 t1 s1_h t_h ∧ vote_msg st v s2 t2 s2_h t_h

/-- サラウンド投票によるスラッシング

validatorは、一方の投票のソースとターゲットが
他方の投票のソースとターゲットの間に厳密に挟まれる
2つの投票を行ってはならない。

Coq: `Definition slashed_surround_vote st v := exists s1 t1 s1_h t1_h,
       exists s2 t2 s2_h t2_h, vote_msg st v s1 t1 s1_h t1_h /\
       vote_msg st v s2 t2 s2_h t2_h /\ s2_h > s1_h /\ t2_h < t1_h.`
-/
def slashed_surround_vote (st : State Validator Hash) (v : Validator) : Prop :=
  ∃ (s1 t1 : Hash) (s1_h t1_h : ℕ),
  ∃ (s2 t2 : Hash) (s2_h t2_h : ℕ),
    vote_msg st v s1 t1 s1_h t1_h ∧
    vote_msg st v s2 t2 s2_h t2_h ∧
    s2_h > s1_h ∧ t2_h < t1_h

/-- スラッシングされたvalidator

validatorは、二重投票またはサラウンド投票を行った場合にスラッシングされます。

Coq: `Definition slashed st v : Prop := slashed_double_vote st v \/ slashed_surround_vote st v.`
-/
def slashed (st : State Validator Hash) (v : Validator) : Prop :=
  slashed_double_vote st v ∨ slashed_surround_vote st v

/-
# State - 投票集合としての状態の表現

Coq元ファイル: casper/coq/theories/State.v

## 概要
投票集合としての状態の表現を定義します。

各投票は、ハッシュと高さでソースノードとターゲットノードに名前を付け、
特定のvalidatorによって署名されます。これは元のCasperペーパーで
投票が表現される方法から直接取られています。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Casper.Validator
import Casper.HashTree

/-!
## 投票の定義

投票は以下のタプルです:
  (attestor, source, target, source height, target height)

Coq: `Definition Vote := (Validator * Hash * Hash * nat * nat)%type.`
-/

/-- 投票の型定義 -/
def Vote (Validator Hash : Type) : Type := Validator × Hash × Hash × ℕ × ℕ

/-- 状態は投票された有限集合で記述されます

Coq: `Definition State := {fset Vote}.`
-/
abbrev State (Validator Hash : Type) : Type :=
  Finset (Vote Validator Hash)

section Projections

variable {Validator Hash : Type}

/-!
## 投票述語と射影操作
-/

/-- 投票が状態に属するかを判定する述語

Coq: `Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool := (v,s,t,s_h,t_h) \in st .`
-/
def vote_msg [DecidableEq Validator] [DecidableEq Hash]
    (st : State Validator Hash) (v : Validator) (s t : Hash) (s_h t_h : ℕ) : Prop :=
  (v, s, t, s_h, t_h) ∈ st

/-!
### 投票の射影操作
-/

/-- 投票からvalidatorを取り出す

Coq: `Definition vote_val (v:Vote) : Validator := match v with (x,_,_,_,_) => x end.`
-/
def vote_val (v : Vote Validator Hash) : Validator := v.1

/-- 投票からソースハッシュを取り出す

Coq: `Definition vote_source (v:Vote) : Hash := match v with (_,s,_,_,_) => s end.`
-/
def vote_source (v : Vote Validator Hash) : Hash := v.2.1

/-- 投票からターゲットハッシュを取り出す

Coq: `Definition vote_target (v:Vote) : Hash := match v with (_,_,t,_,_) => t end.`
-/
def vote_target (v : Vote Validator Hash) : Hash := v.2.2.1

/-- 投票からソース高さを取り出す

Coq: `Definition vote_source_height (v:Vote) : nat := match v with (_,_,_,s_h,_) => s_h end.`
-/
def vote_source_height (v : Vote Validator Hash) : ℕ := v.2.2.2.1

/-- 投票からターゲット高さを取り出す

Coq: `Definition vote_target_height (v:Vote) : nat := match v with (_,_,_,_,t_h) => t_h end.`
-/
def vote_target_height (v : Vote Validator Hash) : ℕ := v.2.2.2.2

/-!
## 投票の再構成
-/

/-- 射影を使った投票の再構成

Coq: `Lemma vote_unfold (vote:Vote): vote = ((vote_val vote), (vote_source vote),
       (vote_target vote), (vote_source_height vote), (vote_target_height vote)).`
-/
lemma vote_unfold (vote : Vote Validator Hash) :
    vote = (vote_val vote, vote_source vote, vote_target vote,
            vote_source_height vote, vote_target_height vote) := by
  cases vote with
  | mk v rest =>
    cases rest with
    | mk s rest' =>
      cases rest' with
      | mk t rest'' =>
        cases rest'' with
        | mk s_h t_h =>
          rfl

end Projections

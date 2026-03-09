/-
# HashTree - ブロック（ハッシュ）ツリーの表現と関連する性質

Coq元ファイル: casper/coq/theories/HashTree.v

## 概要
ブロック（ハッシュ）ツリーの表現と関連する性質を定義します。
注意: チェックポイントブロックのツリーを考えるため、"block" は全体を通して
"checkpoint block" を指します。
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

variable {Hash : Type} [Fintype Hash] [DecidableEq Hash]

/-!
## 有限ハッシュ値（ブロック識別子）

Coq: `Parameter Hash : finType.`
-/

-- 親子関係: `hash_parent b b'` (記法 `b <~ b'`) は、
-- ブロックツリーにおいてbがb'の親であることを示します。
-- Coq: `Parameter hash_parent : rel Hash.`
--       `Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).`
variable (hash_parent : Hash → Hash → Prop)

local infixl:50 " <~ " => hash_parent

/-!
## 親子関係の公理
-/

/--
ブロックは自分自身の親にはなれない

Coq: `Axiom hash_parent_irreflexive: forall h1 h2, h1 <~ h2 -> h1 <> h2.`
-/
axiom hash_parent_irreflexive : ∀ h1 h2, h1 <~ h2 → h1 ≠ h2

/--
ブロックは2つの異なる親ブロックを持てない

Coq: `Axiom hash_at_most_one_parent : forall h1 h2 h3, h2 <~ h1 -> h3 <~ h1 -> h2 = h3.`
-/
axiom hash_at_most_one_parent : ∀ h1 h2 h3, h2 <~ h1 → h3 <~ h1 → h2 = h3

/-!
## 祖先関係: `<~` の反射推移閉包
-/

/--
祖先関係 `<~*`: `<~` の反射推移閉包

Coq: `Definition hash_ancestor h1 h2 := connect hash_parent h1 h2.`
      `Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).`
-/
def hash_ancestor (h1 h2 : Hash) : Prop := Relation.ReflTransGen (hash_parent) h1 h2

local infixl:50 " <~* " => hash_ancestor hash_parent

/-!
## ジェネシスブロック

Coq: `Parameter genesis : Hash.`
-/
variable (genesis : Hash)

/-!
## 祖先関係の基本性質

反射推移閉包 "ReflTransGen" から継承される複数の性質を使用します。
他の証明内で hash_ancestor 定義を展開するのではなく、これらの補題を定義します。
-/

/--
ブロックは自分自身の祖先

Coq: `Lemma hash_self_ancestor : forall h, h <~* h.`
-/
lemma hash_self_ancestor (h : Hash) : h <~* h :=
  Relation.ReflTransGen.refl

/--
親ブロックは真の祖先ブロック

Coq: `Lemma hash_parent_ancestor : forall h1 h2, h1 <~ h2 -> h1 <~* h2 /\ h1 <> h2.`
-/
lemma hash_parent_ancestor (h1 h2 : Hash) (hp : h1 <~ h2) :
    h1 <~* h2 ∧ h1 ≠ h2 := by
  constructor
  · exact Relation.ReflTransGen.single hp
  · exact hash_parent_irreflexive hash_parent h1 h2 hp

/--
祖先の親は祖先

Coq: `Lemma hash_ancestor_stepL : forall h1 h2 h3, h1 <~ h2 -> h2 <~* h3 -> h1 <~* h3.`
-/
lemma hash_ancestor_stepL (h1 h2 h3 : Hash) (hp : h1 <~ h2) (ha : h2 <~* h3) :
    h1 <~* h3 :=
  Relation.ReflTransGen.head hp ha

/--
親の祖先は祖先

Coq: `Lemma hash_ancestor_stepR : forall h1 h2 h3, h1 <~* h2 -> h2 <~ h3 -> h1 <~* h3.`
-/
lemma hash_ancestor_stepR (h1 h2 h3 : Hash) (ha : h1 <~* h2) (hp : h2 <~ h3) :
    h1 <~* h3 :=
  Relation.ReflTransGen.tail ha hp

/--
祖先の祖先は祖先

Coq: `Lemma hash_ancestor_concat : forall h1 h2 h3, h1 <~* h2 -> h2 <~* h3 -> h1 <~* h3.`
-/
lemma hash_ancestor_concat (h1 h2 h3 : Hash) (ha1 : h1 <~* h2) (ha2 : h2 <~* h3) :
    h1 <~* h3 :=
  Relation.ReflTransGen.trans ha1 ha2

/--
ブロックは自分自身と競合しない

Coq: `Lemma hash_nonancestor_nonequal: forall h1 h2, h1 </~* h2 -> h1 <> h2.`
-/
lemma hash_nonancestor_nonequal (h1 h2 : Hash) (hna : ¬ h1 <~* h2) : h1 ≠ h2 := by
  intro heq
  apply hna
  rw [heq]
  exact hash_self_ancestor hash_parent h2

/--
競合するブロックはそのブロックの祖先に属せない

Coq: `Lemma hash_ancestor_conflict: forall h1 h2 p, h1 <~* h2 -> p </~* h2 -> p </~* h1.`
-/
lemma hash_ancestor_conflict (h1 h2 p : Hash)
    (ha : h1 <~* h2) (hn2 : ¬ p <~* h2) : ¬ p <~* h1 := by
  intro hp
  apply hn2
  exact hash_ancestor_concat hash_parent p h1 h2 hp ha

/-!
## nth_ancestor: 祖先関係の段数を明示する定義
-/

/--
n段の祖先関係を明示する帰納的定義

Coq: `Inductive nth_ancestor : nat -> Hash -> Hash -> Prop`
-/
inductive NthAncestor : ℕ → Hash → Hash → Prop where
  | zero : ∀ h1, NthAncestor 0 h1 h1
  | succ : ∀ n h1 h2 h3,
      NthAncestor n h1 h2 → hash_parent h2 h3 →
      NthAncestor (n + 1) h1 h3

/--
nth_ancestorは祖先である

Coq: `Lemma nth_ancestor_ancestor : forall n s t, nth_ancestor n s t -> (s <~* t).`
-/
lemma nth_ancestor_ancestor (n : ℕ) (s t : Hash) (h : NthAncestor hash_parent n s t) :
    s <~* t := by
  induction h
  case zero => exact hash_self_ancestor hash_parent _
  case succ n' h1' h2' h3' hp2 ih =>
    exact Relation.ReflTransGen.tail ih hp2

/--
0段のnth_ancestorは自分自身のみ

Coq: `Lemma nth_ancestor_0_refl : forall h1 h2, nth_ancestor 0 h1 h2 -> h1 = h2.`
-/
lemma nth_ancestor_0_refl (h1 h2 : Hash) (h : NthAncestor hash_parent 0 h1 h2) : h1 = h2 := by
  cases h
  rfl

/--
親は1段の祖先

Coq: `Example parent_ancestor : forall h1 h2, h1 <~ h2 <-> nth_ancestor 1 h1 h2.`
-/
example (h1 h2 : Hash) : h1 <~ h2 ↔ NthAncestor hash_parent 1 h1 h2 := by
  constructor
  · intro hp
    have h0 : NthAncestor hash_parent 0 h1 h1 := NthAncestor.zero h1
    exact NthAncestor.succ 0 h1 h1 h2 h0 hp
  · intro hn
    cases hn with
    | succ n _ hb hc h0 hp =>
      have : _ = hb := nth_ancestor_0_refl hash_parent _ hb h0
      subst this
      exact hp

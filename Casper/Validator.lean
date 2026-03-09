/-
# Validator - Validatorとvalidator stake

Coq元ファイル: casper/coq/theories/Validator.v

## 概要
有限型のValidatorとそのstake（重み）を定義します。

## Coqからの変更点
- `Parameter stake : {fmap Validator -> nat}` を `variable (stake : Validator → ℕ)` に変更
- stakeを全域関数として定義することで、`Axiom st_fun` が不要になりました
- Coqの `stake.[st_fun v]` は Lean4 では単に `stake v` となります
-/

import Mathlib.Data.Fintype.Basic

/-!
## Validators と validator stake

有限集合のvalidatorsを仮定します。
-/

-- 有限型のValidator (Coq: `Parameter Validator : finType.`)
variable (Validator : Type) [Fintype Validator]

-- validatorのstake（重み）を定義する関数 (Coq: `Parameter stake : {fmap Validator -> nat}.`)
-- 注意: 重みは自然数です
-- Lean4では、stakeを全域関数として定義することで、
-- Coqの部分関数 + 全域性公理の組み合わせを置き換えます。
variable (stake : Validator → ℕ)

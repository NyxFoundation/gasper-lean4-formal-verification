/-
# SetTheoryProps - 集合論の性質

Coq の casper/coq/theories/SetTheoryProps.v から翻訳

仕様で使用される様々な集合論的性質を定義します。
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Casper.SetTheoryProps

open Finset

variable {T : Type*} [DecidableEq T]

/-! ## Disjoint 性の補題 -/

/-- A ∩ B と A \ B は disjoint -/
theorem setID_disjoint (A B : Finset T) : Disjoint (A ∩ B) (A \ B) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_inter, mem_sdiff] at ha hb
  exact hb.2 ha.2

/-- A \ B と B \ A は disjoint -/
theorem setDD_disjoint (A B : Finset T) : Disjoint (A \ B) (B \ A) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_sdiff] at ha hb
  exact ha.2 hb.1

/-- (A \ B) ∪ (B \ A) と A ∩ B は disjoint -/
theorem setDDI_disjoint (A B : Finset T) : Disjoint ((A \ B) ∪ (B \ A)) (A ∩ B) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_union, mem_sdiff, mem_inter] at ha hb
  cases ha with
  | inl h => exact h.2 hb.2
  | inr h => exact h.2 hb.1

/-! ## Union の分割 -/

/-- A ∪ B = (A \ B) ∪ (B \ A) ∪ (A ∩ B) -/
theorem setU_par (A B : Finset T) : A ∪ B = (A \ B) ∪ (B \ A) ∪ (A ∩ B) := by
  ext x
  simp only [mem_union, mem_sdiff, mem_inter]
  constructor
  · intro h
    cases h with
    | inl ha =>
      by_cases hb : x ∈ B
      · right; exact ⟨ha, hb⟩
      · left; left; exact ⟨ha, hb⟩
    | inr hb =>
      by_cases ha : x ∈ A
      · right; exact ⟨ha, hb⟩
      · left; right; exact ⟨hb, ha⟩
  · intro h
    rcases h with ((hab | hba) | habi)
    · exact Or.inl hab.1
    · exact Or.inr hba.1
    · exact Or.inl habi.1

/-! ## Disjoint の保存 -/

/-- A と B が disjoint なら、A と B ∩ C も disjoint -/
theorem setIs_disjoint (A B C : Finset T) (h : Disjoint A B) : Disjoint A (B ∩ C) := by
  apply disjoint_of_subset_right inter_subset_left h

/-- (A ∩ B) と (A ∩ C \ B) は disjoint -/
theorem setIID_disjoint (A B C : Finset T) : Disjoint (A ∩ B) (A ∩ (C \ B)) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_inter, mem_sdiff] at ha hb
  exact hb.2.2 ha.2

/-- 複雑な disjoint の補題 -/
theorem setIIDD_disjoint (A B C D : Finset T) :
    Disjoint ((A ∩ B) ∪ (A ∩ (C \ B))) ((B ∩ D) \ A) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_union, mem_inter, mem_sdiff] at ha hb
  cases ha with
  | inl h => exact hb.2 h.1
  | inr h => exact hb.2 h.1

/-! ## Subset の補題 -/

/-- 複雑な subset の補題 -/
theorem setIIDD_subset (A B C D : Finset T) (Ha : A ⊆ C) (Hb : B ⊆ D) :
    (A ∩ B) ∪ (A ∩ (D \ B)) ∪ ((B ∩ C) \ A) ⊆ C ∩ D := by
  intro x hx
  simp only [mem_union, mem_inter, mem_sdiff] at hx ⊢
  rcases hx with ((hab | had) | hbc)
  · exact ⟨Ha hab.1, Hb hab.2⟩
  · exact ⟨Ha had.1, had.2.1⟩
  · exact ⟨hbc.1.2, Hb hbc.1.1⟩

/-- A ∩ C と B \ C は disjoint -/
theorem setID2_disjoint (A B C : Finset T) : Disjoint (A ∩ C) (B \ C) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_inter, mem_sdiff] at ha hb
  exact hb.2 ha.2

/-- A ⊆ B なら A ⊆ (A ∩ C) ∪ (B \ C) -/
theorem setID2_subset (A B C : Finset T) (h : A ⊆ B) : A ⊆ (A ∩ C) ∪ (B \ C) := by
  intro x hx
  simp only [mem_union, mem_inter, mem_sdiff]
  by_cases hc : x ∈ C
  · left; exact ⟨hx, hc⟩
  · right; exact ⟨h hx, hc⟩

/-- C \ B と A \ C は disjoint -/
theorem set3D_disjoint (A B C : Finset T) : Disjoint (C \ B) (A \ C) := by
  rw [disjoint_left]
  intro a ha hb
  simp [mem_sdiff] at ha hb
  exact hb.2 ha.1

/-- A \ B ⊆ C \ B ∪ A \ C -/
theorem set3D_subset (A B C : Finset T) : A \ B ⊆ (C \ B) ∪ (A \ C) := by
  intro x hx
  simp only [mem_sdiff, mem_union] at hx ⊢
  by_cases hc : x ∈ C
  · left; exact ⟨hc, hx.2⟩
  · right; exact ⟨hx.1, hc⟩

end Casper.SetTheoryProps

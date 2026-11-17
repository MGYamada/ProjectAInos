/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Variational.FieldJet.Basic
import Mathlib.Tactic.Ring

/-!
# The Euler operators of a jet ring of fields

Because the total derivatives commute, the iterated total derivative `D^K` of a multi-index
`K` is well defined (`iterTotalDeriv`). The Euler operator of the field `a` is
`Eₐ = Σ_K (−1)^{|K|} D^K ∂ᵃ_K`, a finite sum on every element.

* `euler_totalDeriv`: `Eₐ (D_μ F) = 0`: a divergence is a null Lagrangian.
* `euler_add_totalDeriv`: adding a total derivative to a Lagrangian does not change its
  Euler–Lagrange expressions.

No section, integral or limit appears.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Variational.FieldJetRing

open SmoothAlgebra

variable {ι κ J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype κ] [DecidableEq ι]
  (R : FieldJetRing ι κ J)

instance : LeftCommutative fun (μ : ι) (F : J) => R.totalDeriv μ F :=
  ⟨fun μ ν F => totalDeriv_comm μ ν F⟩

/-- The iterated total derivative `D^K` of a multi-index. -/
def iterTotalDeriv (K : Multiset ι) (F : J) : J :=
  Multiset.foldr (fun μ G => R.totalDeriv μ G) F K

variable {R}

@[simp] theorem iterTotalDeriv_zero (F : J) : R.iterTotalDeriv 0 F = F := rfl

theorem iterTotalDeriv_cons (μ : ι) (K : Multiset ι) (F : J) :
    R.iterTotalDeriv (μ ::ₘ K) F = R.totalDeriv μ (R.iterTotalDeriv K F) :=
  Multiset.foldr_cons _ _ _ _

/-- `D^K` commutes with a total derivative. -/
theorem iterTotalDeriv_totalDeriv (K : Multiset ι) (μ : ι) (F : J) :
    R.iterTotalDeriv K (R.totalDeriv μ F) = R.totalDeriv μ (R.iterTotalDeriv K F) := by
  induction K using Multiset.induction with
  | empty => rfl
  | cons ν K ih => rw [iterTotalDeriv_cons, iterTotalDeriv_cons, ih, totalDeriv_comm]

theorem iterTotalDeriv_add (K : Multiset ι) (F G : J) :
    R.iterTotalDeriv K (F + G) = R.iterTotalDeriv K F + R.iterTotalDeriv K G := by
  induction K using Multiset.induction with
  | empty => rfl
  | cons ν K ih => rw [iterTotalDeriv_cons, iterTotalDeriv_cons, iterTotalDeriv_cons, ih, map_add]

@[simp] theorem iterTotalDeriv_map_zero (K : Multiset ι) : R.iterTotalDeriv K (0 : J) = 0 := by
  induction K using Multiset.induction with
  | empty => rfl
  | cons ν K ih => rw [iterTotalDeriv_cons, ih, map_zero]

/-- The multi-indices of a total derivative: those of the element, and those with one more
index. -/
theorem SupportIn.totalDeriv {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (μ : ι) :
    R.SupportIn (R.totalDeriv μ F) (S ∪ S.image (μ ::ₘ ·)) := by
  intro b L hL
  rw [Finset.mem_union, not_or] at hL
  rw [d_totalDeriv, h b L hL.1, map_zero, zero_add]
  split_ifs with hμ
  · refine h b _ fun hmem => hL.2 ?_
    rw [Finset.mem_image]
    exact ⟨L.erase μ, hmem, Multiset.cons_erase hμ⟩
  · rfl

variable (R)

/-- The Euler operator `Eₐ = Σ_K (−1)^{|K|} D^K ∂ᵃ_K`. -/
def euler (a : κ) (F : J) : J :=
  ∑ᶠ K : Multiset ι, (-1 : J) ^ Multiset.card K * R.iterTotalDeriv K (R.d a K F)

variable {R}

theorem euler_eq_sum {F : J} {S : Finset (Multiset ι)} (h : R.SupportIn F S) (a : κ) :
    R.euler a F = ∑ K ∈ S, (-1 : J) ^ Multiset.card K * R.iterTotalDeriv K (R.d a K F) := by
  apply finsum_eq_sum_of_support_subset
  intro K hK
  rw [Function.mem_support] at hK
  by_contra hS
  apply hK
  rw [h a K (by simpa using hS), iterTotalDeriv_map_zero, mul_zero]

/-- A total derivative is a null Lagrangian: `Eₐ (D_μ F) = 0`. -/
theorem euler_totalDeriv (a : κ) (μ : ι) (F : J) : R.euler a (R.totalDeriv μ F) = 0 := by
  obtain ⟨S, hS⟩ := R.exists_supportIn F
  have hinj : Function.Injective fun K : Multiset ι => μ ::ₘ K := fun K L h =>
    (Multiset.cons_inj_right μ).mp h
  -- the first sum: the terms with the multi-indices of `F`
  have h1 : ∑ K ∈ S ∪ S.image (μ ::ₘ ·),
      (-1 : J) ^ Multiset.card K * R.iterTotalDeriv K (R.totalDeriv μ (R.d a K F)) =
      ∑ K ∈ S, (-1 : J) ^ Multiset.card K * R.iterTotalDeriv (μ ::ₘ K) (R.d a K F) := by
    rw [← Finset.sum_subset Finset.subset_union_left]
    · refine Finset.sum_congr rfl fun K _ => ?_
      rw [iterTotalDeriv_totalDeriv, iterTotalDeriv_cons]
    · intro K _ hK
      rw [hS a K hK, map_zero, iterTotalDeriv_map_zero, mul_zero]
  -- the second sum: the terms with one index removed
  have h2 : ∑ K ∈ S ∪ S.image (μ ::ₘ ·), (-1 : J) ^ Multiset.card K *
        R.iterTotalDeriv K (if μ ∈ K then R.d a (K.erase μ) F else 0) =
      ∑ K ∈ S, (-1 : J) ^ (Multiset.card K + 1) * R.iterTotalDeriv (μ ::ₘ K) (R.d a K F) := by
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := S) (s₂ := S.image (μ ::ₘ ·)))]
    · rw [Finset.sum_image fun K _ L _ h => hinj h]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [Multiset.card_cons]
      simp only [Multiset.mem_cons_self, ↓reduceIte, Multiset.erase_cons_head]
    · intro K _ hK
      split_ifs with hμ
      · have hnot : K.erase μ ∉ S := fun hmem => hK (by
          rw [Finset.mem_image]
          exact ⟨K.erase μ, hmem, Multiset.cons_erase hμ⟩)
        rw [hS a _ hnot, iterTotalDeriv_map_zero, mul_zero]
      · rw [iterTotalDeriv_map_zero, mul_zero]
  rw [euler_eq_sum (hS.totalDeriv μ) a]
  simp only [d_totalDeriv, iterTotalDeriv_add, mul_add, Finset.sum_add_distrib]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun K _ => ?_
  ring

/-- Adding a total derivative does not change the Euler–Lagrange expressions. -/
theorem euler_add_totalDeriv (a : κ) (μ : ι) (L F : J) :
    R.euler a (L + R.totalDeriv μ F) = R.euler a L := by
  obtain ⟨S, hS⟩ := R.exists_supportIn L
  obtain ⟨T, hT⟩ := R.exists_supportIn (R.totalDeriv μ F)
  have hL := hS.mono (Finset.subset_union_left (s₁ := S) (s₂ := T))
  have hF := hT.mono (Finset.subset_union_right (s₁ := S) (s₂ := T))
  have h : R.euler a (R.totalDeriv μ F) = 0 := euler_totalDeriv a μ F
  rw [euler_eq_sum hF] at h
  rw [euler_eq_sum (hL.add hF), euler_eq_sum hL]
  simp only [map_add, iterTotalDeriv_add, mul_add, Finset.sum_add_distrib, h, add_zero]

end ProjectAinos.Variational.FieldJetRing

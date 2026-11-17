/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Variational.FieldJet.Euler
public import ProjectAinos.SmoothAlgebra.FreeDerivation
public import ProjectAinos.SmoothAlgebra.IterPartialDeriv

/-!
# The standard jet ring of fields and the prolongation of a field

The standard jet ring of fields is the free C-infinity ring on the independent variables `x_μ`
and the jet co-ordinates `uᵃ_K` (`StandardFieldJet.jetRing`). It is the instance of the
structure `FieldJetRing`.

For `n` independent variables a field is a family `φ` of smooth functions on `ℝⁿ`. Its
prolongation `StandardFieldJet.prolongation φ` is the morphism of C-infinity rings into the
smooth functions on `ℝⁿ` that substitutes `x_μ` by the co-ordinate and `uᵃ_K` by the iterated
partial derivative `∂^K φᵃ`.

* `prolongation_totalDeriv`: the prolongation carries the total derivative `D_μ` to the
  partial derivative `∂_μ`.
* `IsSolution L φ`: the Euler–Lagrange expressions of `L` vanish on the prolongation of `φ`.
  `isSolution_add_totalDeriv`: a total derivative added to the Lagrangian does not change the
  solutions.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Variational

open SmoothAlgebra SmoothRing

/-- The standard jet ring of fields: the free C-infinity ring on the independent variables
`Sum.inl μ` and the jet co-ordinates `Sum.inr (a, K)`. -/
abbrev StandardFieldJet (ι κ : Type*) := FreeSmoothRing (ι ⊕ κ × Multiset ι)

namespace StandardFieldJet

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The multi-index of a generator. An independent variable has the empty multi-index. -/
def generatorIndex : ι ⊕ κ × Multiset ι → Multiset ι
  | Sum.inl _ => 0
  | Sum.inr p => p.2

variable (ι κ) in
/-- The jet-ring structure of the standard jet ring of fields. -/
def jetRing : FieldJetRing ι κ (StandardFieldJet ι κ) where
  dx μ := FreeSmoothRing.partialDerivation (Sum.inl μ)
  d a K := FreeSmoothRing.partialDerivation (Sum.inr (a, K))
  u a K := FreeSmoothRing.generator (Sum.inr (a, K))
  d_u_self _ _ := FreeSmoothRing.partialDerivation_generator_self _
  d_u_ne _ _ _ _ h :=
    FreeSmoothRing.partialDerivation_generator_of_ne fun hc => h (Sum.inr.inj hc)
  dx_u _ _ _ := FreeSmoothRing.partialDerivation_generator_of_ne (by simp)
  dx_comm _ _ F := FreeSmoothRing.partialDerivation_comm _ _ F
  dx_d_comm _ _ _ F := FreeSmoothRing.partialDerivation_comm _ _ F
  d_comm _ _ _ _ F := FreeSmoothRing.partialDerivation_comm _ _ F
  finite_support F := by
    obtain ⟨T, hT⟩ := FreeSmoothRing.exists_finset_partialDerivation_eq_zero F
    refine ⟨T.image generatorIndex, fun a K hK => hT _ fun hmem => hK ?_⟩
    rw [Finset.mem_image]
    exact ⟨Sum.inr (a, K), hmem, rfl⟩

/-- The independent variable `x_μ` as an element of the jet ring. -/
def x (μ : ι) : StandardFieldJet ι κ := FreeSmoothRing.generator (Sum.inl μ)

variable [Fintype κ]

/-- `D_μ x_ν = δ_{μν}`. -/
theorem totalDeriv_x (μ ν : ι) :
    (jetRing ι κ).totalDeriv μ (x ν) = if ν = μ then 1 else 0 := by
  have hS : (jetRing ι κ).SupportIn (x ν : StandardFieldJet ι κ) ∅ := fun a K _ =>
    FreeSmoothRing.partialDerivation_generator_of_ne (by simp)
  rw [FieldJetRing.totalDeriv_eq_sum μ hS, Finset.sum_empty, add_zero]
  change FreeSmoothRing.partialDerivation (Sum.inl μ) (FreeSmoothRing.generator (Sum.inl ν)) = _
  rw [FreeSmoothRing.partialDerivation_generator]
  by_cases h : ν = μ
  · simp [h]
  · simp [h]

end StandardFieldJet

/-! ### The prolongation of a field -/

namespace StandardFieldJet

variable {n : ℕ} {κ : Type*}

/-- The values of the generators on the prolongation of a field: the co-ordinates and the
iterated partial derivatives of the components. -/
def prolongationValue (φ : κ → SmoothOperation n) :
    Fin n ⊕ κ × Multiset (Fin n) → SmoothOperation n
  | Sum.inl μ => SmoothOperation.proj μ
  | Sum.inr p => SmoothOperation.iterPartialDeriv p.2 (φ p.1)

/-- The prolongation of a field `φ`: the substitution of its jet. -/
def prolongation (φ : κ → SmoothOperation n) :
    SmoothRingHom (StandardFieldJet (Fin n) κ) (SmoothOperation n) :=
  FreeSmoothRing.lift (prolongationValue φ)

@[simp] theorem prolongation_x (φ : κ → SmoothOperation n) (μ : Fin n) :
    prolongation φ (x μ) = SmoothOperation.proj μ :=
  FreeSmoothRing.lift_generator _ _

variable [DecidableEq κ]

@[simp] theorem prolongation_u (φ : κ → SmoothOperation n) (a : κ) (K : Multiset (Fin n)) :
    prolongation φ ((jetRing (Fin n) κ).u a K) = SmoothOperation.iterPartialDeriv K (φ a) :=
  FreeSmoothRing.lift_generator _ _

variable [Fintype κ]

/-- The prolongation carries the total derivative to the partial derivative. -/
theorem prolongation_totalDeriv (φ : κ → SmoothOperation n) (μ : Fin n)
    (F : StandardFieldJet (Fin n) κ) :
    prolongation φ ((jetRing (Fin n) κ).totalDeriv μ F) =
      SmoothOperation.partialDeriv μ (prolongation φ F) := by
  refine FreeSmoothRing.map_derivation_eq (prolongation φ) ((jetRing (Fin n) κ).totalDeriv μ)
    (SmoothDerivation.partialDerivation μ) (fun c => ?_) F
  rcases c with ν | ⟨a, K⟩
  · change prolongation φ ((jetRing (Fin n) κ).totalDeriv μ (x ν)) =
      SmoothOperation.partialDeriv μ (prolongation φ (x ν))
    rw [totalDeriv_x, prolongation_x, SmoothOperation.partialDeriv_proj]
    by_cases h : ν = μ
    · simp [h]
    · simp [h, Ne.symm h]
  · change prolongation φ ((jetRing (Fin n) κ).totalDeriv μ ((jetRing (Fin n) κ).u a K)) =
      SmoothOperation.partialDeriv μ (prolongation φ ((jetRing (Fin n) κ).u a K))
    rw [FieldJetRing.totalDeriv_u, prolongation_u, prolongation_u,
      SmoothOperation.iterPartialDeriv_cons]

/-- A field is a solution of the Lagrangian `L` if the Euler–Lagrange expressions vanish on
its prolongation. -/
def IsSolution (L : StandardFieldJet (Fin n) κ) (φ : κ → SmoothOperation n) : Prop :=
  ∀ a, prolongation φ ((jetRing (Fin n) κ).euler a L) = 0

/-- A total derivative added to the Lagrangian does not change the solutions. -/
theorem isSolution_add_totalDeriv (L F : StandardFieldJet (Fin n) κ) (μ : Fin n)
    (φ : κ → SmoothOperation n) :
    IsSolution (L + (jetRing (Fin n) κ).totalDeriv μ F) φ ↔ IsSolution L φ := by
  unfold IsSolution
  simp only [FieldJetRing.euler_add_totalDeriv]

end StandardFieldJet

end ProjectAinos.Variational

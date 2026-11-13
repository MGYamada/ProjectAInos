/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

/-! # A finite qubit comparison prototype

Rays and positive normalized linear functionals are defined independently.
The vector-to-state comparison is proved through the normalized outer product.
`Ket` is a coordinate vector space; its Hilbert realization is `Hilbert` (the
ordinary Pi norm on `Ket` is not asserted to be the Hilbert norm).
No Fubini--Study, purity classification, or GNS theorem is assumed here.
-/

@[expose] public section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace ProjectAInos.QuantumMechanics.Qubit

abbrev Ket := Fin 2 → ℂ
abbrev Hilbert := EuclideanSpace ℂ (Fin 2)
abbrev Operator := Matrix (Fin 2) (Fin 2) ℂ
abbrev Observable := {A : Operator // A.IsHermitian}
abbrev NonzeroKet := {v : Ket // v ≠ 0}
abbrev Ray := Projectivization ℂ Ket

/-- The standard Hermitian pairing in coordinates. -/
def pairing (v w : Ket) : ℂ := star v ⬝ᵥ w

theorem pairing_eq_inner (v w : Ket) :
    pairing v w = inner ℂ (WithLp.toLp 2 v : Hilbert) (WithLp.toLp 2 w : Hilbert) := by
  exact dotProduct_comm _ _

theorem pairing_adjoint (A : Operator) (v w : Ket) :
    pairing (A *ᵥ v) w = pairing v (Aᴴ *ᵥ w) := by
  simp only [pairing, star_mulVec, dotProduct_mulVec]

/-- Squared Hilbert length, retained in ℂ for scalar algebra. -/
def weight (v : Ket) : ℂ := pairing v v

theorem weight_pos (v : NonzeroKet) : 0 < weight v :=
  Matrix.dotProduct_star_self_pos_iff.mpr v.property

theorem weight_ne_zero (v : NonzeroKet) : weight v ≠ 0 := ne_of_gt (weight_pos v)

/-- Positive normalized complex-linear functionals on the full matrix algebra.
Positivity is the intrinsic Mathlib positive-semidefinite cone, not membership
in the image of vector states. Complex order also enforces zero imaginary part. -/
structure State where
  functional : Operator →ₗ[ℂ] ℂ
  normalized : functional 1 = 1
  positive : ∀ A, A.PosSemidef → 0 ≤ functional A

@[ext] theorem State.ext {s t : State} (h : s.functional = t.functional) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- Geometric expectation, initially on nonzero representatives. -/
def expectation (v : NonzeroKet) (A : Operator) : ℂ :=
  (weight v)⁻¹ * pairing v (A *ᵥ v)

/-- Normalized rank-one outer product. -/
def projector (v : NonzeroKet) : Operator :=
  (weight v)⁻¹ • vecMulVec (v : Ket) (star (v : Ket))

theorem projector_posSemidef (v : NonzeroKet) : (projector v).PosSemidef :=
  (posSemidef_vecMulVec_self_star (v : Ket)).smul
    (RCLike.inv_pos_of_pos (weight_pos v)).le

theorem projector_isHermitian (v : NonzeroKet) : (projector v).IsHermitian :=
  (projector_posSemidef v).isHermitian

theorem projector_trace (v : NonzeroKet) : (projector v).trace = 1 := by
  rw [projector, trace_smul, trace_vecMulVec, dotProduct_comm]
  exact inv_mul_cancel₀ (weight_ne_zero v)

theorem projector_mulVec (v : NonzeroKet) (w : Ket) :
    projector v *ᵥ w = ((weight v)⁻¹ * pairing v w) • (v : Ket) := by
  ext i
  simp [projector, pairing, mulVec, dotProduct, vecMulVec]
  ring

theorem projector_fixes (v : NonzeroKet) : projector v *ᵥ (v : Ket) = v := by
  rw [projector_mulVec]
  change ((weight v)⁻¹ * weight v) • (v : Ket) = v
  rw [inv_mul_cancel₀ (weight_ne_zero v), one_smul]

theorem projector_idempotent (v : NonzeroKet) : projector v * projector v = projector v := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [← Matrix.mulVec_mulVec, projector_mulVec v w, mulVec_smul, projector_fixes]

/-- The image is exactly the line through v: a genuine rank-one assertion. -/
theorem projector_range (v : NonzeroKet) :
    LinearMap.range (projector v).mulVecLin = Submodule.span ℂ {(v : Ket)} := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    rw [mulVecLin_apply, projector_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro w hw
    have hw' : w = (v : Ket) := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨v, projector_fixes v⟩

theorem projector_finrank (v : NonzeroKet) :
    Module.finrank ℂ (LinearMap.range (projector v).mulVecLin) = 1 := by
  rw [projector_range]
  exact finrank_span_singleton v.property

/-- Algebraic trace and geometric pairing agree; neither is defined via the other. -/
theorem trace_projector_mul (v : NonzeroKet) (A : Operator) :
    (projector v * A).trace = expectation v A := by
  simp only [projector, smul_mul_assoc, trace_smul, vecMulVec_mul, trace_vecMulVec,
    expectation, pairing, smul_eq_mul]
  rw [dotProduct_comm, ← dotProduct_mulVec]

def vectorState (v : NonzeroKet) : State where
  functional :=
    { toFun := fun A => (projector v * A).trace
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp }
  normalized := by simpa using projector_trace v
  positive A hA := by
    change 0 ≤ (projector v * A).trace
    rw [trace_projector_mul]
    exact mul_nonneg (RCLike.inv_pos_of_pos (weight_pos v)).le
      (hA.dotProduct_mulVec_nonneg v)

theorem vectorState_expectation (v : NonzeroKet) (A : Operator) :
    (vectorState v).functional A = expectation v A := trace_projector_mul v A

theorem expectation_real (v : NonzeroKet) (A : Observable) :
    (expectation v A).im = 0 := by
  have hw : star (weight v) = weight v := (weight_pos v).le.isSelfAdjoint.star_eq
  have he : star (expectation v A) = expectation v A := by
    simp only [expectation, star_mul, star_inv₀, hw, pairing]
    rw [A.property.star_dotProduct_mulVec_comm]
    exact mul_comm _ _
  exact Complex.conj_eq_iff_im.mp he

def rescale (c : ℂ) (hc : c ≠ 0) (v : NonzeroKet) : NonzeroKet :=
  ⟨c • (v : Ket), smul_ne_zero hc v.property⟩

theorem weight_smul (c : ℂ) (v : Ket) :
    weight (c • v) = (star c * c) * weight v := by
  simp [weight, pairing, star_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, mul_assoc]
  ring

theorem projector_rescale (c : ℂ) (hc : c ≠ 0) (v : NonzeroKet) :
    projector (rescale c hc v) = projector v := by
  ext i j
  simp only [projector, rescale, weight_smul, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply, Pi.star_apply, Pi.smul_apply, star_mul]
  have hsc : star c ≠ 0 := star_ne_zero.mpr hc
  field_simp [hc, hsc]

theorem expectation_rescale (c : ℂ) (hc : c ≠ 0) (v : NonzeroKet) (A : Operator) :
    expectation (rescale c hc v) A = expectation v A := by
  rw [← trace_projector_mul, ← trace_projector_mul, projector_rescale]

theorem projector_eq_iff_ray (v w : NonzeroKet) :
    projector v = projector w ↔ Projectivization.mk' ℂ v = Projectivization.mk' ℂ w := by
  constructor
  · intro h
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk,
      Projectivization.mk_eq_mk_iff']
    refine ⟨(weight w)⁻¹ * pairing w v, ?_⟩
    rw [← projector_mulVec, ← h, projector_fixes]
  · intro h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ v.property w.property).mp h
    have hc0 : c ≠ 0 := by
      intro h0
      apply v.property
      simpa [h0] using hc.symm
    have hv : v = rescale c hc0 w := Subtype.ext hc.symm
    rw [hv, projector_rescale]

def rayProjector : Ray → Operator :=
  Projectivization.lift projector fun a b c h => by
    apply (projector_eq_iff_ray a b).mpr
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ a.property b.property).mpr ⟨c, h.symm⟩

@[simp] theorem rayProjector_mk (v : NonzeroKet) :
    rayProjector (Projectivization.mk' ℂ v) = projector v := rfl

theorem rayProjector_injective : Function.Injective rayProjector := by
  intro x y h
  induction x using Projectivization.ind with | h v hv =>
    induction y using Projectivization.ind with | h w hw =>
      exact (projector_eq_iff_ray ⟨v, hv⟩ ⟨w, hw⟩).mp h

theorem vectorState_eq_iff_projector (v w : NonzeroKet) :
    vectorState v = vectorState w ↔ projector v = projector w := by
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro A
    exact congrArg (fun s : State => s.functional A) h
  · intro h
    apply State.ext
    apply LinearMap.ext
    intro A
    exact congrArg (fun P : Operator => (P * A).trace) h

theorem vectorState_eq_iff_ray (v w : NonzeroKet) :
    vectorState v = vectorState w ↔ Projectivization.mk' ℂ v = Projectivization.mk' ℂ w :=
  (vectorState_eq_iff_projector v w).trans (projector_eq_iff_ray v w)

def rayState : Ray → State :=
  Projectivization.lift vectorState fun a b c h => by
    apply (vectorState_eq_iff_ray a b).mpr
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ a.property b.property).mpr ⟨c, h.symm⟩

@[simp] theorem rayState_mk (v : NonzeroKet) :
    rayState (Projectivization.mk' ℂ v) = vectorState v := rfl

theorem rayState_injective : Function.Injective rayState := by
  intro x y h
  induction x using Projectivization.ind with | h v hv =>
    induction y using Projectivization.ind with | h w hw =>
      exact (vectorState_eq_iff_ray ⟨v, hv⟩ ⟨w, hw⟩).mp h

/-- This is a vector-state equivalence, NOT a purity-classification theorem. -/
def rayEquivVectorStates : Ray ≃ Set.range rayState := Equiv.ofInjective _ rayState_injective

/-- An intrinsic matrix type: no vector or ray occurs in its definition. -/
abbrev RankOneProjector := {P : Operator // P.IsHermitian ∧ P * P = P ∧
  Module.finrank ℂ (LinearMap.range P.mulVecLin) = 1}

theorem exists_projector (P : RankOneProjector) : ∃ v : NonzeroKet, projector v = P.val := by
  obtain ⟨u, hu, hspan⟩ := finrank_eq_one_iff'.mp P.property.2.2
  let v : NonzeroKet := ⟨u.val, fun h => hu (Subtype.ext h)⟩
  have hfix : P.val *ᵥ (v : Ket) = v := by
    obtain ⟨w, hw⟩ := u.property
    change P.val *ᵥ u.val = u.val
    rw [← hw]
    change P.val *ᵥ (P.val *ᵥ w) = P.val *ᵥ w
    rw [mulVec_mulVec, P.property.2.1]
  refine ⟨v, Matrix.ext_iff_mulVec.mpr fun w => ?_⟩
  obtain ⟨c, hc⟩ := hspan ⟨P.val *ᵥ w, ⟨w, rfl⟩⟩
  have hc' : c • (v : Ket) = P.val *ᵥ w := congrArg Subtype.val hc
  have hp : pairing v w = c * weight v := by
    calc
      pairing v w = pairing (P.val *ᵥ v) w := by rw [hfix]
      _ = pairing v (P.val *ᵥ w) := by rw [pairing_adjoint, P.property.1.eq]
      _ = c * weight v := by rw [← hc']; simp [pairing, weight, dotProduct_smul]
  rw [projector_mulVec, hp]
  have hcancel : (weight v)⁻¹ * (c * weight v) = c := by
    field_simp [weight_ne_zero v]
  rw [hcancel]
  exact hc'

def rayRankOneProjector (r : Ray) : RankOneProjector :=
  ⟨rayProjector r, by
    induction r using Projectivization.ind with | h v hv =>
      exact ⟨projector_isHermitian ⟨v, hv⟩, projector_idempotent ⟨v, hv⟩,
        projector_finrank ⟨v, hv⟩⟩⟩

/-- Full bijection with intrinsic rank-one orthogonal projectors.
This remains distinct from classifying the extreme points of all `State`s. -/
def rayEquivRankOneProjectors : Ray ≃ RankOneProjector :=
  Equiv.ofBijective rayRankOneProjector ⟨
    fun _ _ h => rayProjector_injective (congrArg Subtype.val h),
    fun P => by
      obtain ⟨v, hv⟩ := exists_projector P
      exact ⟨Projectivization.mk' ℂ v, Subtype.ext hv⟩⟩

end ProjectAInos.QuantumMechanics.Qubit

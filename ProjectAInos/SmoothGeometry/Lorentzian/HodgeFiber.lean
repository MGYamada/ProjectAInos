/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.VolumeForm
public import ProjectAInos.SmoothGeometry.DifferentialForm.HodgeTransport

/-! # Intrinsic Lorentz Hodge duality on the actual tangent fibres

Metric duality supplies the nondegenerate cotangent metric. The constructed
oriented volume supplies its normalization. The defining wedge equation and
uniqueness hold on every tangent fibre without a chosen frame or chart.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- The metric duality equivalence with the algebraic dual of the actual tangent space. -/
def algebraicFlat (g : LorentzMetric σ d M) (x : M) :
    TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃ₗ[ℝ] Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :=
  (g.flat x).toLinearEquiv.trans LinearMap.toContinuousLinearMap.symm

def coMetricEquiv (g : LorentzMetric σ d M) (x : M) :
    Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x) ≃ₗ[ℝ]
      Dual ℝ (Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)) :=
  (g.algebraicFlat x).symm.trans (Module.evalEquiv ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x))

/-- The inverse metric on algebraic covectors, induced by the existing `sharp`. -/
def coMetric (g : LorentzMetric σ d M) (x : M) :
    LinearMap.BilinForm ℝ (Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)) :=
  (g.coMetricEquiv x).toLinearMap

theorem coMetric_bijective (g : LorentzMetric σ d M) (x : M) :
    Function.Bijective (g.coMetric x) := (g.coMetricEquiv x).bijective

theorem coMetric_apply (g : LorentzMetric σ d M) (x : M)
    (α β : Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)) :
    g.coMetric x α β = β (g.sharp x (LinearMap.toContinuousLinearMap α)) := rfl

theorem coMetric_symmetric (g : LorentzMetric σ d M) (x : M) : LinearMap.IsSymm (g.coMetric x) := by
  constructor
  intro α β
  obtain ⟨v, rfl⟩ := (g.algebraicFlat x).surjective α
  obtain ⟨w, rfl⟩ := (g.algebraicFlat x).surjective β
  change (g.algebraicFlat x w) ((g.algebraicFlat x).symm (g.algebraicFlat x v)) =
    (g.algebraicFlat x v) ((g.algebraicFlat x).symm (g.algebraicFlat x w))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact g.symmetric x w v

theorem opposite_coMetric (g : LorentzMetric σ d M) (x : M) :
    g.opposite.coMetric x = -g.coMetric x := by
  ext α β
  change β (g.opposite.sharp x (LinearMap.toContinuousLinearMap α)) =
    -β (g.sharp x (LinearMap.toContinuousLinearMap α))
  rw [g.opposite_sharp_apply, map_neg]

omit [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
/-- The top cotangent degree agrees with the declared spacetime dimension. -/
theorem cotangent_topDegree (x : M) :
    d + 1 = Module.finrank ℝ (Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)) := by
  simp [TangentSpace, MinkowskiModel]

/-- The oriented volume with its top degree made explicit for exterior duality. -/
def hodgeTopVolume (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M) :
    TangentSpace 𝓘(ℝ, MinkowskiModel d) x
      [⋀^Fin (Module.finrank ℝ (Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)))]→L[ℝ] ℝ :=
  finiteDegreeCast (cotangent_topDegree x) (g.volumeForm o x)

theorem hodgeTopVolume_ne_zero (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M) :
    g.hodgeTopVolume o x ≠ 0 := finiteDegreeCast_ne_zero _ (g.volumeForm_ne_zero o x)

/-- The Lorentz Hodge equivalence on a native tangent fibre. -/
def hodgeFiber (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (x : M) {k l : ℕ} (hkl : k + l = d + 1) :
    (TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ]
      (TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin l]→L[ℝ] ℝ) :=
  finiteHodgeOfDegree (g.coMetric x) (g.coMetric_bijective x) (g.volumeForm o x)
    (g.volumeForm_ne_zero o x) (cotangent_topDegree x) hkl

/-- The induced inverse-metric pairing on arbitrary alternating covectors. -/
def formPairing (g : LorentzMetric σ d M) (x : M) {k : ℕ}
    (α β : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) : ℝ :=
  (g.coMetric x).exteriorPower k (finiteToExterior α) (finiteToExterior β)

theorem formPairing_symmetric (g : LorentzMetric σ d M) (x : M) {k : ℕ}
    (α β : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) :
    g.formPairing x α β = g.formPairing x β α :=
  (exteriorPower_symmetric (g.coMetric x) (g.coMetric_symmetric x) k).eq _ _

/-- The standard wedge--metric defining equation, on actual tangent forms. -/
theorem hodgeFiber_wedge (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (x : M) {k l : ℕ} (hkl : k + l = d + 1)
    (α β : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) :
    finiteDegreeCast hkl (finiteWedge α (g.hodgeFiber o x hkl β)) =
      g.formPairing x α β • g.volumeForm o x := by
  apply finiteDegreeCast_injective (cotangent_topDegree x)
  rw [finiteDegreeCast_trans, finiteDegreeCast_smul]
  exact finiteHodge_wedge_symmetric (g.coMetric x) (g.coMetric_bijective x)
    (g.hodgeTopVolume o x) (g.hodgeTopVolume_ne_zero o x) (g.coMetric_symmetric x)
    (hkl.trans (cotangent_topDegree x)) α β

/-- Uniqueness is equality of the actual fibrewise forms. -/
theorem hodgeFiber_unique (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (x : M) {k l : ℕ} (hkl : k + l = d + 1)
    (β : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ)
    (γ : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin l]→L[ℝ] ℝ)
    (h : ∀ α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ,
      finiteDegreeCast hkl (finiteWedge α γ) = g.formPairing x α β • g.volumeForm o x) :
    γ = g.hodgeFiber o x hkl β := by
  apply finiteHodgeOfDegree_unique
  intro α
  change finiteDegreeCast hkl (finiteWedge α γ) = g.formPairing x β α • g.volumeForm o x
  rw [g.formPairing_symmetric x β α]
  exact h α

/-- Pointwise Hodge on a native field; smoothness is a separate regularity theorem. -/
def nativeHodge (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) (α : NativeForm 𝓘(ℝ, MinkowskiModel d) M k) :
    NativeForm 𝓘(ℝ, MinkowskiModel d) M l := fun x => g.hodgeFiber o x hkl (α x)

/-- The constructed native wedge satisfies the Hodge--metric identity pointwise. -/
theorem nativeHodge_wedge (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) (α β : NativeForm 𝓘(ℝ, MinkowskiModel d) M k) (x : M) :
    finiteDegreeCast hkl (nativeWedge α (g.nativeHodge o hkl β) x) =
      g.formPairing x (α x) (β x) • g.volumeForm o x := by
  rw [nativeWedge_eq_finiteWedge]
  exact g.hodgeFiber_wedge o x hkl (α x) (β x)

theorem hodgeTopVolume_reverse (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M) :
    g.hodgeTopVolume o.reverse x = -g.hodgeTopVolume o x := by
  have h := congrArg (fun a : SmoothForm 𝓘(ℝ, MinkowskiModel d) M (d + 1) => a x)
    (g.volumeForm_reverse o)
  change g.volumeForm o.reverse x = -g.volumeForm o x at h
  unfold hodgeTopVolume
  rw [h, finiteDegreeCast_neg]

/-- Reversing orientation negates Lorentz Hodge in every degree. -/
theorem hodgeFiber_reverse (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (x : M) {k l : ℕ} (hkl : k + l = d + 1)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) :
    g.hodgeFiber o.reverse x hkl α = -g.hodgeFiber o x hkl α := by
  change finiteHodge (g.coMetric x) (g.coMetric_bijective x) (g.hodgeTopVolume o.reverse x)
    _ _ α = -finiteHodge (g.coMetric x) (g.coMetric_bijective x) (g.hodgeTopVolume o x) _ _ α
  calc
    _ = finiteHodge (g.coMetric x) (g.coMetric_bijective x) (-g.hodgeTopVolume o x)
        (neg_ne_zero.mpr (g.hodgeTopVolume_ne_zero o x)) (hkl.trans (cotangent_topDegree x)) α :=
      finiteHodge_congr_volume (g.coMetric x) (g.coMetric_bijective x) _ _ _ _
        (g.hodgeTopVolume_reverse o x) _ α
    _ = _ := finiteHodge_reverse_volume (g.coMetric x) (g.coMetric_bijective x)
      (g.hodgeTopVolume o x) (g.hodgeTopVolume_ne_zero o x) _ α

theorem opposite_hodgeTopVolume (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M) :
    g.opposite.hodgeTopVolume o x = g.hodgeTopVolume o x := by
  unfold hodgeTopVolume
  rw [g.opposite_volumeForm]

/-- Whole-metric sign reversal contributes `(-1)^k` on degree-`k` forms. -/
theorem hodgeFiber_opposite (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (x : M) {k l : ℕ} (hkl : k + l = d + 1)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) :
    g.opposite.hodgeFiber o x hkl α = (-1 : ℝ) ^ k • g.hodgeFiber o x hkl α := by
  change finiteHodge (g.opposite.coMetric x) (g.opposite.coMetric_bijective x)
    (g.opposite.hodgeTopVolume o x) _ _ α = _
  have hB : g.opposite.coMetric x = (-1 : ℝ) • g.coMetric x :=
    (g.opposite_coMetric x).trans (_root_.neg_one_smul ℝ (g.coMetric x)).symm
  calc
    _ = finiteHodge (g.opposite.coMetric x) (g.opposite.coMetric_bijective x)
        (g.hodgeTopVolume o x) (g.hodgeTopVolume_ne_zero o x)
        (hkl.trans (cotangent_topDegree x)) α :=
      finiteHodge_congr_volume (g.opposite.coMetric x) (g.opposite.coMetric_bijective x)
        _ _ _ _ (g.opposite_hodgeTopVolume o x) _ α
    _ = _ := finiteHodge_scale_metric (g.coMetric x) (g.coMetric_bijective x)
      (g.hodgeTopVolume o x) (g.hodgeTopVolume_ne_zero o x)
      (g.opposite.coMetric x) (g.opposite.coMetric_bijective x) (-1) hB _ α

section Naturality
variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]

/-- The inverse metric transforms covariantly on pulled-back cotangent vectors. -/
theorem coMetric_naturality (g : LorentzMetric σ d M) (h : LorentzMetric σ d N) (x : M) (y : N)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (hmetric : ∀ v w, g.form x v w = h.form y (L v) (L w))
    (α β : Dual ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) y)) :
    g.coMetric x (L.toLinearMap.dualMap α) (L.toLinearMap.dualMap β) = h.coMetric y α β := by
  change β (L (g.sharp x ((LinearMap.toContinuousLinearMap α).comp L.toContinuousLinearMap))) =
    β (h.sharp y (LinearMap.toContinuousLinearMap α))
  rw [g.sharp_naturality h x y L hmetric, L.apply_symm_apply]

/-- A metric- and oriented-volume-preserving tangent equivalence commutes with Hodge. -/
theorem hodgeFiber_naturality (g : LorentzMetric σ d M) (h : LorentzMetric σ d N)
    (o : OrientedAtlas (d + 1) M) (o' : OrientedAtlas (d + 1) N) (x : M) (y : N)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (hmetric : ∀ v w, g.form x v w = h.form y (L v) (L w))
    (hvolume : (h.volumeForm o' y).compContinuousLinearMap L.toContinuousLinearMap = g.volumeForm o x)
    {k l : ℕ} (hkl : k + l = d + 1)
    (β : TangentSpace 𝓘(ℝ, MinkowskiModel d) y [⋀^Fin k]→L[ℝ] ℝ) :
    (h.hodgeFiber o' y hkl β).compContinuousLinearMap L.toContinuousLinearMap =
      g.hodgeFiber o x hkl (β.compContinuousLinearMap L.toContinuousLinearMap) :=
  finiteHodgeOfDegree_natural (g.coMetric x) (g.coMetric_bijective x)
    (h.coMetric y) (h.coMetric_bijective y) (g.volumeForm o x) (g.volumeForm_ne_zero o x)
    (cotangent_topDegree x) (h.volumeForm o' y) (h.volumeForm_ne_zero o' y)
    (cotangent_topDegree y) L (g.coMetric_naturality h x y L hmetric) hvolume hkl β

end Naturality

end ProjectAInos.SmoothGeometry.LorentzMetric

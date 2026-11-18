/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.Killing

/-! Public consumers of the Lorentz metrics from coordinate coefficients: the criterion for the
signature of a symmetric bilinear form in every dimension and for both conventions, the chart of
an open set of the model space, the Lorentz metric of a coordinate metric with its components,
its inverse and its Christoffel symbols, the constant Minkowski metric, the spatial form of a
timelike observer with the radar measurement and the spatial metric of an observer at rest, and
the Killing fields with the conservation of their pairing along geodesics and the red shift.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

namespace ProjectAinos.SmoothGeometry.Minkowski

example {d : ℕ} {U W : MinkowskiModel d}
    (hU : 0 < intervalQuadratic U) (hW : pair U W = 0) (hW0 : W ≠ 0) :
    intervalQuadratic W < 0 :=
  intervalQuadratic_neg_of_pair_eq_zero hU hW hW0

end ProjectAinos.SmoothGeometry.Minkowski

open ContinuousLinearMap
open ContinuousLinearMap
namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

example (Q : QuadraticForm ℝ (Fin d → ℝ))
    (hQ : ∀ v ≠ 0, 0 < Q v) :
    ∃ e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ), ∀ v, Q v = ∑ i, (e v i) ^ 2 :=
  exists_linearEquiv_sum_sq Q hQ

example (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v)
    (ht : B (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < B (Fin.cons 0 v) (Fin.cons 0 v)) :
    ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w) :=
  exists_lorentzFrame B hs ht hx

example (σ : LorentzConvention)
    (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v)
    (ht : -σ.timeSign * B (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < -σ.timeSign * B (Fin.cons 0 v) (Fin.cons 0 v)) :
    ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, B v w = minkowskiForm σ d (e v) (e w) :=
  exists_lorentzFrame_convention σ B hs ht hx

end ProjectAinos.SmoothGeometry.Minkowski

open Bundle ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology
namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

example {U : Opens (MinkowskiModel d)} (x y : U) :
    physicalChart x = physicalChart y :=
  physicalChart_eq x y

example {U : Opens (MinkowskiModel d)} (x y : U) :
    physicalChart x y = (y : MinkowskiModel d) :=
  physicalChart_apply x y

example {U : Opens (MinkowskiModel d)} (x : U) :
    (physicalChart x).source = univ :=
  physicalChart_source x

example {U : Opens (MinkowskiModel d)} (x : U) :
    (physicalChart x).target = (U : Set (MinkowskiModel d)) :=
  physicalChart_target x

example {U : Opens (MinkowskiModel d)} (x : U) :
    physicalChart x ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ U :=
  physicalChart_mem x

example {U : Opens (MinkowskiModel d)} (x y : U) :
    (trivializationAt (MinkowskiModel d) (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x).symmL ℝ y =
      (ContinuousLinearMap.id ℝ (MinkowskiModel d) : MinkowskiModel d →L[ℝ] MinkowskiModel d) :=
  physicalChart_symmL x y

example {U : Opens (MinkowskiModel d)} (x y : U)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    chartTangentMap (physicalChart x) y v = (v : MinkowskiModel d) :=
  physicalChart_tangentMap x y v

end CoordinateMetric

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)

example (x : U) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.toLorentzMetric.form x v w = g.form x v w :=
  toLorentzMetric_form g x v w

example (x y : U) (v : MinkowskiModel d) :
    (chartField (physicalChart x) v y : MinkowskiModel d) = v :=
  physicalChart_chartField x y v

example (x y : U) (v w : MinkowskiModel d) :
    g.toLorentzMetric.chartMetric (physicalChart x) y v w = g.form y v w :=
  toLorentzMetric_chartMetric g x y v w

example (x y : U) (i j : Fin (d + 1)) :
    g.toLorentzMetric.chartComponent (physicalChart x) y i j =
      g.form y (Pi.single i 1) (Pi.single j 1) :=
  toLorentzMetric_chartComponent g x y i j

example (y v w : MinkowskiModel d) :
    g.form y v w = ∑ i, ∑ j, g.coefficient y i j * v i * w j :=
  form_apply g y v w

example {y : MinkowskiModel d} (hy : y ∈ U) (i j : Fin (d + 1)) :
    g.coefficient y i j = g.coefficient y j i :=
  coefficient_symmetric g hy i j

example (i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun y => g.coefficient y i j) U :=
  coefficient_contDiffOn g i j

example (x y : U) :
    g.coefficient y * Matrix.of (g.toLorentzMetric.inverseComponent y
      (chartTangentEquiv (physicalChart_mem x) (by simp))) = 1 :=
  coefficient_mul_inverseComponent g x y

example (x y : U) (i j : Fin (d + 1)) :
    g.toLorentzMetric.inverseComponent y
        (chartTangentEquiv (physicalChart_mem x) (by simp)) i j =
      (g.coefficient y)⁻¹ i j :=
  toLorentzMetric_inverseComponent g x y i j

example (y : U) : g.coefficient y * (g.coefficient y)⁻¹ = 1 :=
  coefficient_mul_inv g y

example (x y : U) (i j : Fin (d + 1))
    (v : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d)
        (fun z => g.toLorentzMetric.chartComponent (physicalChart x) z i j)
        y (chartField (physicalChart x) v y) =
      fderiv ℝ (fun z => g.coefficient z i j) y v :=
  toLorentzMetric_component_derivative g x y i j v

example (x y : U) (k i j : Fin (d + 1)) :
    g.toLorentzMetric.chartChristoffel (physicalChart x) y k i j =
      ∑ l, (g.coefficient y)⁻¹ k l *
        (fderiv ℝ (fun z => g.coefficient z j l) y (Pi.single i 1) +
         fderiv ℝ (fun z => g.coefficient z l i) y (Pi.single j 1) -
         fderiv ℝ (fun z => g.coefficient z i j) y (Pi.single l 1)) / 2 :=
  toLorentzMetric_christoffel g x y k i j

example
    (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (Fin.cons 0 v) (Fin.cons 0 v)) :
    (ofCriterion B hB hs ht hx).form = B :=
  ofCriterion_form B hB hs ht hx

example (x y : U) (i j : Fin (d + 1)) :
    (minkowski σ d U).toLorentzMetric.chartComponent (physicalChart x) y i j =
      if i = j then lorentzSign σ i else 0 :=
  minkowski_chartComponent x y i j

example (g : CoordinateMetric .timeNegative d U) {x : MinkowskiModel d}
    (hx : x ∈ U) (h00 : g.form x (Pi.single 0 1) (Pi.single 0 1) < 0) {ξ : Fin d → ℝ}
    (hξ : ξ ≠ 0) : 0 < ∑ i, ∑ j, Minkowski.spatialMetric (g.form x) i j * ξ i * ξ j :=
  spatialMetric_pos g hx h00 hξ

end CoordinateMetric

namespace LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

example (g : LorentzMetric .timeNegative d M) (x : M)
    {u : TangentSpace 𝓘(ℝ, MinkowskiModel d) x} (hu : g.form x u u < 0)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    0 ≤ Minkowski.spatialForm (g.form x) u v v :=
  spatialForm_nonneg g x hu v

example (g : LorentzMetric .timeNegative d M) (x : M)
    {u v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x} (hu : g.form x u u < 0)
    (hv : Minkowski.orthogonalPart (g.form x) u v ≠ 0) :
    0 < Minkowski.spatialForm (g.form x) u v v :=
  spatialForm_pos g x hu hv

end LorentzMetric

end ProjectAinos.SmoothGeometry

open ContinuousLinearMap
namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

variable (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

example (u v w : MinkowskiModel d) :
    spatialForm B u v w = B v w - B u v * B u w / B u u :=
  spatialForm_apply B u v w

variable {B}

example {u : MinkowskiModel d} (hu : B u u ≠ 0)
    (v : MinkowskiModel d) : B u (orthogonalPart B u v) = 0 :=
  orthogonalPart_orthogonal hu v

example (hs : ∀ v w, B v w = B w v) {u : MinkowskiModel d} (hu : B u u ≠ 0)
    (v w : MinkowskiModel d) :
    spatialForm B u v w = B (orthogonalPart B u v) (orthogonalPart B u w) :=
  spatialForm_eq hs hu v w

example {u : MinkowskiModel d} (hu : B u u ≠ 0) (w : MinkowskiModel d) :
    spatialForm B u u w = 0 :=
  spatialForm_self_left hu w

example (hs : ∀ v w, B v w = B w v) {u : MinkowskiModel d}
    (hu : B u u ≠ 0) (v : MinkowskiModel d) : spatialForm B u v u = 0 :=
  spatialForm_self_right hs hu v

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) (v w : MinkowskiModel d) :
    B v w = B w v :=
  symm_of_frame he v w

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) (v w : MinkowskiModel d) :
    B v w = -pair (e v) (e w) :=
  neg_form_eq_pair he v w

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u v : MinkowskiModel d}
    (hu : B u u < 0) (hv : B u v = 0) (hv0 : v ≠ 0) : 0 < B v v :=
  pos_of_orthogonal he hu hv hv0

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u : MinkowskiModel d}
    (hu : B u u < 0) (v : MinkowskiModel d) : 0 ≤ spatialForm B u v v :=
  spatialForm_nonneg he hu v

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u v : MinkowskiModel d}
    (hu : B u u < 0) (hv : orthogonalPart B u v ≠ 0) : 0 < spatialForm B u v v :=
  spatialForm_pos he hu hv

example (hs : ∀ v w, B v w = B w v) (u v : MinkowskiModel d) (τ : ℝ) :
    B (v - τ • u) (v - τ • u) = B v v - 2 * τ * B u v + τ ^ 2 * B u u :=
  form_sub_smul hs u v τ

example (hs : ∀ v w, B v w = B w v) {u v : MinkowskiModel d} (hu : B u u ≠ 0)
    {τ₁ τ₂ : ℝ} (hne : τ₁ ≠ τ₂) (h₁ : B (v - τ₁ • u) (v - τ₁ • u) = 0)
    (h₂ : B (v - τ₂ • u) (v - τ₂ • u) = 0) :
    -B u u * ((τ₂ - τ₁) / 2) ^ 2 = spatialForm B u v v ∧
      B u (v - ((τ₁ + τ₂) / 2) • u) = 0 :=
  radar hs hu hne h₁ h₂

example (hs : ∀ v w, B v w = B w v) {u v : MinkowskiModel d} (hu : B u u < 0)
    {τ₁ τ₂ : ℝ} (h12 : τ₁ < τ₂) (h₁ : B (v - τ₁ • u) (v - τ₁ • u) = 0)
    (h₂ : B (v - τ₂ • u) (v - τ₂ • u) = 0) :
    Real.sqrt (-B u u) * (τ₂ - τ₁) / 2 = Real.sqrt (spatialForm B u v v) :=
  radar_distance hs hu h12 h₁ h₂

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u v : MinkowskiModel d}
    (hu : B u u < 0) (hv : orthogonalPart B u v ≠ 0) :
    ∃ τ₁ τ₂ : ℝ, τ₁ < τ₂ ∧ B (v - τ₁ • u) (v - τ₁ • u) = 0 ∧
      B (v - τ₂ • u) (v - τ₂ • u) = 0 :=
  exists_radar he hu hv

example (v : MinkowskiModel d) :
    v = v 0 • Pi.single 0 1 + ∑ i : Fin d, v i.succ • Pi.single i.succ 1 :=
  eq_time_add_space v

example (i j : Fin d) :
    spatialMetric B i j =
      spatialForm B (Pi.single 0 1) (Pi.single i.succ 1) (Pi.single j.succ 1) :=
  spatialMetric_eq i j

example (hs : ∀ v w, B v w = B w v)
    (h00 : B (Pi.single 0 1) (Pi.single 0 1) ≠ 0) (v w : MinkowskiModel d) :
    spatialForm B (Pi.single 0 1) v w = ∑ i, ∑ j, spatialMetric B i j * v i.succ * w j.succ :=
  spatialForm_timeAxis hs h00 v w

example {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w))
    (h00 : B (Pi.single 0 1) (Pi.single 0 1) < 0) {ξ : Fin d → ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ i, ∑ j, spatialMetric B i j * ξ i * ξ j :=
  spatialMetric_pos he h00 hξ

example (h00 : B (Pi.single 0 1) (Pi.single 0 1) ≠ 0)
    (v : MinkowskiModel d) :
    B (Pi.single 0 1) v = 0 ↔
      v 0 = -(∑ i : Fin d, B (Pi.single 0 1) (Pi.single i.succ 1) * v i.succ) /
        B (Pi.single 0 1) (Pi.single 0 1) :=
  orthogonal_timeAxis_iff h00 v

end ProjectAinos.SmoothGeometry.Minkowski

open Bundle Set TopologicalSpace VectorField
open scoped Manifold ContDiff Topology
namespace ProjectAinos.SmoothGeometry

namespace LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

example {g : LorentzMetric σ d M}
    {K : ∀ x : M, TangentSpace I x} (hK : g.IsKillingField K) (x : M) (v : TangentSpace I x) :
    g.form x (g.leviCivita K x v) v = 0 :=
  IsKillingField.form_leviCivita_self hK x v

example {g : LorentzMetric σ d M}
    {K : ∀ x : M, TangentSpace I x} (hK : g.IsKillingField K)
    (hKd : ∀ x, MDifferentiableAt I ((I).prod I) (T% K) x) {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn s γ) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun r => g.form (γ r) (K (γ r)) (curveVelocity γ r)) 0 t :=
  IsKillingField.hasDerivAt_pairing hK hKd hγ ht

example {g : LorentzMetric σ d M} {K : ∀ x : M, TangentSpace I x}
    (hK : g.IsKillingField K) (hKd : ∀ x, MDifferentiableAt I ((I).prod I) (T% K) x)
    {γ : ℝ → M} {s : Set ℝ} (hγ : g.IsGeodesicOn s γ) (hs : Convex ℝ s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) :
    g.form (γ a) (K (γ a)) (curveVelocity γ a) = g.form (γ b) (K (γ b)) (curveVelocity γ b) :=
  IsKillingField.pairing_eq hK hKd hγ hs ha hb

example {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x} {x : M} (hx : g.form x (K x) (K x) < 0) :
    0 < g.killingNorm K x :=
  killingNorm_pos hx

example {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x}
    {x : M} (hx : g.form x (K x) (K x) < 0) :
    g.form x (g.stationaryVelocity K x) (g.stationaryVelocity K x) = -1 :=
  form_stationaryVelocity hx

example {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x}
    {γ : ℝ → M} {t : ℝ}
    (ht : g.form (γ t) (K (γ t)) (K (γ t)) < 0) :
    g.killingNorm K (γ t) * g.observedFrequency K γ t =
      -g.form (γ t) (K (γ t)) (curveVelocity γ t) :=
  killingNorm_mul_observedFrequency ht

example {g : LorentzMetric .timeNegative d M}
    {K : ∀ x : M, TangentSpace I x}
    (hK : g.IsKillingField K)
    (hKd : ∀ x, MDifferentiableAt I ((I).prod I) (T% K) x) {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn s γ) (hs : Convex ℝ s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hta : g.form (γ a) (K (γ a)) (K (γ a)) < 0) (htb : g.form (γ b) (K (γ b)) (K (γ b)) < 0) :
    g.killingNorm K (γ a) * g.observedFrequency K γ a =
      g.killingNorm K (γ b) * g.observedFrequency K γ b :=
  killingNorm_mul_observedFrequency_eq hK hKd hγ hs ha hb hta htb

variable {σ' : LorentzConvention}

example (g : LorentzMetric σ' d M) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (k : Fin (d + 1))
    (h : ∀ i j, mvfderiv I (fun y => g.chartComponent e y i j) x
      (chartField e (Pi.single k 1) x) = 0) (v w : TangentSpace I x) :
    g.form x (g.leviCivita (chartField e (Pi.single k 1)) x v) w +
      g.form x v (g.leviCivita (chartField e (Pi.single k 1)) x w) = 0 :=
  killing_chartField_of g he hx k h v w

end LorentzMetric

namespace CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example (g : CoordinateMetric σ d U) (x₀ : U) (k : Fin (d + 1))
    (h : ∀ y ∈ U, ∀ i j, fderiv ℝ (fun z => g.coefficient z i j) y (Pi.single k 1) = 0) :
    g.toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single k 1)) :=
  isKillingField_chartField g x₀ k h

example {f : MinkowskiModel d → ℝ} {y v : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f y) (h : ∀ t : ℝ, f (y + t • v) = f y) : fderiv ℝ f y v = 0 :=
  fderiv_eq_zero_of_invariant hf h

example (g : CoordinateMetric σ d U) (x₀ : U) (k : Fin (d + 1))
    (h : ∀ (y : MinkowskiModel d) (t : ℝ), g.form (y + t • Pi.single k 1) = g.form y) :
    g.toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single k 1)) :=
  isKillingField_of_invariant g x₀ k h

example (x₀ y : U) (v : MinkowskiModel d) :
    MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) ((𝓘(ℝ, MinkowskiModel d)).prod 𝓘(ℝ, MinkowskiModel d))
      (T% (chartField (physicalChart x₀) v)) y :=
  chartField_mdifferentiableAt x₀ y v

end CoordinateMetric

end ProjectAinos.SmoothGeometry

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.NormalGeodesics
import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
import ProjectAinos.GeneralRelativity.DeSitterSlicing

/-! Public consumers of the synchronous reference system: the lemma of Gauss for a family of
geodesics with the same metric norm of their velocity, the synchronous coordinate metrics with
their inverse, Christoffel symbols, time lines and Ricci tensor, and de Sitter space in the flat
slicing with `Ric = 3 g`. Default elaborator options are intentional: these checks must not rely
on the implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

open Bundle Set Filter

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

local notation "J" => 𝓘(ℝ, ℝ × ℝ)

example (g : LorentzMetric σ d M) {Γ : ℝ × ℝ → M} {s₁ s₂ s₀ τ c : ℝ} (hs₀ : s₀ ∈ Ioo s₁ s₂)
    (hτ : 0 ≤ τ) (hreg : ∀ s ∈ Ioo s₁ s₂, ∀ t ∈ Icc 0 τ, ContMDiffAt J I 2 Γ (s, t))
    (hgeo : ∀ s ∈ Ioo s₁ s₂, g.IsGeodesicOn (Icc 0 τ) (fun t => Γ (s, t)))
    (hnorm : ∀ s ∈ Ioo s₁ s₂, g.form (Γ (s, 0)) (curveVelocity (fun t => Γ (s, t)) 0)
      (curveVelocity (fun t => Γ (s, t)) 0) = c) :
    ∀ t ∈ Icc 0 τ, g.form (Γ (s₀, t)) (curveVelocity (fun t => Γ (s₀, t)) t)
        (familyVelocity Γ (1, 0) (s₀, t)) =
      g.form (Γ (s₀, 0)) (curveVelocity (fun t => Γ (s₀, t)) 0)
        (familyVelocity Γ (1, 0) (s₀, 0)) :=
  familyVelocity_pairing_eq g hs₀ hτ hreg hgeo hnorm

example (g : LorentzMetric σ d M) {Γ : ℝ × ℝ → M} {s₁ s₂ s₀ τ c : ℝ} (hs₀ : s₀ ∈ Ioo s₁ s₂)
    (hτ : 0 ≤ τ) (hreg : ∀ s ∈ Ioo s₁ s₂, ∀ t ∈ Icc 0 τ, ContMDiffAt J I 2 Γ (s, t))
    (hgeo : ∀ s ∈ Ioo s₁ s₂, g.IsGeodesicOn (Icc 0 τ) (fun t => Γ (s, t)))
    (hnorm : ∀ s ∈ Ioo s₁ s₂, g.form (Γ (s, 0)) (curveVelocity (fun t => Γ (s, t)) 0)
      (curveVelocity (fun t => Γ (s, t)) 0) = c)
    (horth : g.form (Γ (s₀, 0)) (curveVelocity (fun t => Γ (s₀, t)) 0)
      (familyVelocity Γ (1, 0) (s₀, 0)) = 0) :
    ∀ t ∈ Icc 0 τ, g.form (Γ (s₀, t)) (curveVelocity (fun t => Γ (s₀, t)) t)
      (familyVelocity Γ (1, 0) (s₀, t)) = 0 :=
  familyVelocity_orthogonal g hs₀ hτ hreg hgeo hnorm horth

end ProjectAinos.SmoothGeometry.LorentzMetric

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

example (g : CoordinateMetric .timeNegative d U) :
    Prop :=
  IsSynchronous g

example (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) (α β : Fin d) :
    ℝ :=
  extrinsicRate g z α β

example (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) (α β : Fin d) :
    ℝ :=
  metricRate g z α β

example (g : CoordinateMetric .timeNegative d U) (z : MinkowskiModel d) (α β : Fin d) :
    ℝ :=
  sliceRicci g z α β

example (g : CoordinateMetric .timeNegative d U) {z : MinkowskiModel d} (hz : z ∈ U)
    (k : Fin (d + 1)) :
    fderiv ℝ (fun w => Real.log (densityOf g.coefficient w)) z (Pi.single k 1) =
      ∑ c, christoffelOf g.coefficient z c c k :=
  fderiv_log_densityOf g hz k

namespace IsSynchronous

variable {g : CoordinateMetric .timeNegative d U} (hs : g.IsSynchronous) {z : MinkowskiModel d}

example (hz : z ∈ U) (l : Fin (d + 1)) :
    g.coefficient z 0 l = if l = 0 then -1 else 0 :=
  coefficient_zero hs hz l

example (hz : z ∈ U) (l : Fin (d + 1)) :
    g.coefficient z l 0 = if l = 0 then -1 else 0 :=
  coefficient_zero_right hs hz l

example (hz : z ∈ U) (j : Fin (d + 1)) :
    (g.coefficient z)⁻¹ 0 j = if j = 0 then -1 else 0 :=
  inv_zero hs hz j

example (hz : z ∈ U) (j : Fin (d + 1)) :
    (g.coefficient z)⁻¹ j 0 = if j = 0 then -1 else 0 :=
  inv_zero_right hs hz j

example (hz : z ∈ U) (l : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun w => g.coefficient w 0 l) z v = 0 :=
  fderiv_coefficient_zero hs hz l v

example (hz : z ∈ U) (l : Fin (d + 1)) (v : MinkowskiModel d) :
    fderiv ℝ (fun w => g.coefficient w l 0) z v = 0 :=
  fderiv_coefficient_zero_right hs hz l v

example (hz : z ∈ U) (k : Fin (d + 1)) :
    christoffelOf g.coefficient z k 0 0 = 0 :=
  christoffel_zero_zero hs hz k

example (hz : z ∈ U) (j : Fin (d + 1)) :
    christoffelOf g.coefficient z 0 0 j = 0 :=
  christoffel_zero_zero_succ hs hz j

example (hz : z ∈ U) (j : Fin (d + 1)) :
    christoffelOf g.coefficient z 0 j 0 = 0 :=
  christoffel_zero_succ_zero hs hz j

example (hz : z ∈ U) (α β : Fin d) :
    christoffelOf g.coefficient z α.succ 0 β.succ = g.extrinsicRate z α β / 2 :=
  christoffel_succ_zero_succ hs hz α β

example (hz : z ∈ U) (α β : Fin d) :
    christoffelOf g.coefficient z α.succ β.succ 0 = g.extrinsicRate z α β / 2 :=
  christoffel_succ_succ_zero hs hz α β

example (hz : z ∈ U) :
    ricciOf g.coefficient z 0 0 =
      -(∑ α, fderiv ℝ (fun w => g.extrinsicRate w α α) z (Pi.single 0 1)) / 2 -
        (∑ α, ∑ β, g.extrinsicRate z α β * g.extrinsicRate z β α) / 4 :=
  ricci_zero_zero hs hz

example (hz : z ∈ U) (α β : Fin d) :
    christoffelOf g.coefficient z 0 α.succ β.succ = g.metricRate z α β / 2 :=
  christoffel_zero_succ_succ hs hz α β

example (hz : z ∈ U) (α : Fin d) :
    ricciOf g.coefficient z 0 α.succ =
      (∑ β, (fderiv ℝ (fun w => g.extrinsicRate w β α) z (Pi.single β.succ 1) +
          ∑ γ : Fin d, (christoffelOf g.coefficient z β.succ β.succ γ.succ *
              g.extrinsicRate z γ α -
            christoffelOf g.coefficient z γ.succ β.succ α.succ * g.extrinsicRate z β γ)) -
        ∑ β, fderiv ℝ (fun w => g.extrinsicRate w β β) z (Pi.single α.succ 1)) / 2 :=
  ricci_zero_succ hs hz α

example (hz : z ∈ U) (α β : Fin d) :
    ricciOf g.coefficient z α.succ β.succ =
      g.sliceRicci z α β + fderiv ℝ (fun w => g.metricRate w α β) z (Pi.single 0 1) / 2 +
        (∑ γ, (g.extrinsicRate z γ γ * g.metricRate z α β -
          g.metricRate z α γ * g.extrinsicRate z γ β -
          g.extrinsicRate z γ α * g.metricRate z γ β)) / 4 :=
  ricci_succ_succ hs hz α β

example {γ : ℝ → U} {s : Set ℝ} (hso : IsOpen s) {z₀ : MinkowskiModel d}
    (hγ : ∀ t ∈ s, (γ t : MinkowskiModel d) = z₀ + t • Pi.single 0 1) :
    g.toLorentzMetric.IsGeodesicOn s γ ∧ ∀ t ∈ s,
      g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = -1 ∧
        ∀ α : Fin d, g.toLorentzMetric.form (γ t) (curveVelocity γ t) (Pi.single α.succ 1) = 0 :=
  isGeodesicOn_timeLine hs hso hγ

end IsSynchronous

end ProjectAinos.SmoothGeometry.CoordinateMetric

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.DeSitterSlicing

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3

example (q : E) (i : Fin 4) :
    ℝ :=
  coefficients q i

example (q : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  form q

example (q v w : E) :
    form q v w = ∑ i, coefficients q i * (v i * w i) :=
  form_apply q v w

example :
    ContDiff ℝ ∞ form :=
  contDiff_form

example (q : E) (i : Fin 4) :
    (if i = 0 then (1 : ℝ) else Real.exp (q 0)) ≠ 0 :=
  scaleFactor_ne_zero q i

example (q : E) :
    E ≃ₗ[ℝ] E :=
  scaleLinear q

example (q : E) :
    E ≃L[ℝ] E :=
  scale q

example (q v : E) (i : Fin 4) :
    scale q v i = (if i = 0 then 1 else Real.exp (q 0)) * v i :=
  scale_apply q v i

example :
    CoordinateMetric .timeNegative 3 ⊤ :=
  metric

example (z : E) :
    metric.coefficient z = Matrix.diagonal (coefficients z) :=
  coefficient_eq z

example (z : E) :
    (metric.coefficient z)⁻¹ =
      Matrix.diagonal fun i => if i = 0 then -1 else Real.exp (-(2 * z 0)) :=
  coefficient_inv_eq z

example :
    metric.IsSynchronous :=
  isSynchronous

example (w : E) (α β : Fin 3) :
    metric.coefficient w α.succ β.succ = if α = β then Real.exp (2 * w 0) else 0 :=
  coefficient_succ w α β

example (z : E) :
    HasFDerivAt (fun w : E => Real.exp (2 * w 0))
      (Real.exp (2 * z 0) • (2 : ℝ) • (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ)) z :=
  hasFDerivAt_exp z

example (z : E) (α β : Fin 3) :
    metric.metricRate z α β = if α = β then 2 * Real.exp (2 * z 0) else 0 :=
  metricRate_eq z α β

example (z : E) (α β : Fin 3) :
    metric.extrinsicRate z α β = if α = β then 2 else 0 :=
  extrinsicRate_eq z α β

example (w : E) (i j : Fin 4) (k : Fin 3) :
    fderiv ℝ (fun v => metric.coefficient v i j) w (Pi.single k.succ 1) = 0 :=
  fderiv_coefficient_spatial w i j k

example (w : E) (γ α β : Fin 3) :
    christoffelOf metric.coefficient w γ.succ α.succ β.succ = 0 :=
  christoffel_spatial w γ α β

example (z : E) (α β : Fin 3) (v : E) :
    fderiv ℝ (fun w => metric.extrinsicRate w α β) z v = 0 :=
  fderiv_extrinsicRate z α β v

example (z : E) (i j : Fin 4) :
    ricciOf metric.coefficient z i j = 3 * metric.coefficient z i j :=
  ricci_eq z i j

end ProjectAinos.GeneralRelativity.DeSitterSlicing

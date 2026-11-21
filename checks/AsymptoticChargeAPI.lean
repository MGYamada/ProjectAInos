/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorFlux
import ProjectAinos.GeneralRelativity.AsymptoticCharge

/-! Public consumers of the energy and momentum of the gravitational field at large distances
(Landau–Lifshitz §§96, 105): the superpotential flux and the divergence theorem on spheres and
shells, the decay of the pseudotensor for metrics Galilean at spatial infinity, the charges as
limits of surface integrals with the shell identity, `P⁰ = M` for the isotropic far metric, and
the conservation of the charges when the flux vanishes. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section


section PF

open MeasureTheory Set Metric Real Filter

open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Sphere

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {O : Set (ℝ × E3)} (hO : IsOpen O) {s₀ : ℝ} (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O) :
    ∃ δ > 0, ∀ s, |s - s₀| ≤ δ → ∀ n ∈ sphere (0 : E3) 1, (s, n) ∈ O :=
  exists_prod_subset hO hs₀

example {G : ℝ → E3 → ℝ} {O : Set (ℝ × E3)} (hG : ContinuousOn (Function.uncurry G) O) {s : ℝ}
    (hs : ∀ n ∈ sphere (0 : E3) 1, (s, n) ∈ O) :
    Continuous fun n : sphere (0 : E3) 1 => G s n :=
  continuous_restrict_sphere hG hs

example {G : ℝ → E3 → ℝ} {O : Set (ℝ × E3)} (hO : IsOpen O) {s₀ : ℝ}
    (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O) (hG : ContinuousOn (Function.uncurry G) O) :
    ContinuousAt (fun s => ∫ n : sphere (0 : E3) 1, G s n ∂sphereMeasure) s₀ :=
  continuousAt_integral_sphere hO hs₀ hG

example {F F' : ℝ → E3 → ℝ} {O : Set (ℝ × E3)} (hO : IsOpen O) {s₀ : ℝ}
    (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O) (hF : ContinuousOn (Function.uncurry F) O)
    (hF' : ContinuousOn (Function.uncurry F') O)
    (hd : ∀ p ∈ O, HasDerivAt (fun s => F s p.2) (F' p.1 p.2) p.1) :
    HasDerivAt (fun s => ∫ n : sphere (0 : E3) 1, F s n ∂sphereMeasure)
      (∫ n : sphere (0 : E3) 1, F' s₀ n ∂sphereMeasure) s₀ :=
  hasDerivAt_integral_sphere hO hs₀ hF hF' hd

example (j k : Fin 3) (θ : ℝ) (v : E3) :
    E3 :=
  rotation j k θ v

example (j k : Fin 3) (θ : ℝ) (v : E3) :
    E3 :=
  rotationDeriv j k θ v

example (j k : Fin 3) (v : E3) :
    E3 :=
  angular j k v

example (j k : Fin 3) (v : E3) :
    rotation j k 0 v = v :=
  rotation_zero j k v

example (j k : Fin 3) (v : E3) :
    rotationDeriv j k 0 v = angular j k v :=
  rotationDeriv_zero j k v

example (j k : Fin 3) (θ : ℝ) (v : E3) :
    HasDerivAt (fun θ => rotation j k θ v) (rotationDeriv j k θ v) θ :=
  hasDerivAt_rotation j k θ v

example (j k : Fin 3) :
    Continuous fun p : ℝ × E3 => rotation j k p.1 p.2 :=
  continuous_rotation j k

example (j k : Fin 3) :
    Continuous fun p : ℝ × E3 => rotationDeriv j k p.1 p.2 :=
  continuous_rotationDeriv j k

example (j k : Fin 3) (θ : ℝ) (v w : E3) :
    rotation j k θ (v + w) = rotation j k θ v + rotation j k θ w :=
  rotation_add j k θ v w

example (j k : Fin 3) (θ c : ℝ) (v : E3) :
    rotation j k θ (c • v) = c • rotation j k θ v :=
  rotation_smul j k θ c v

example {j k : Fin 3} (hjk : j ≠ k) (θ : ℝ) (v : E3) :
    ‖rotation j k θ v‖ = ‖v‖ :=
  norm_rotation hjk θ v

example {j k : Fin 3} (hjk : j ≠ k) (θ : ℝ) :
    E3 ≃ₗᵢ[ℝ] E3 :=
  rotationIsometry hjk θ

example {j k : Fin 3} (hjk : j ≠ k) (θ : ℝ) (v : E3) :
    rotationIsometry hjk θ v = rotation j k θ v :=
  rotationIsometry_apply hjk θ v

example {X : Type*} [TopologicalSpace X] {G : E3 → X} {W : Set E3} (hG : ContinuousOn G W) {r : ℝ}
    (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    Continuous fun n : sphere (0 : E3) 1 => G (r • (n : E3)) :=
  continuous_comp_smul_sphere hG hr

example {F : E3 → ℝ} {W : Set E3} (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W) {r : ℝ}
    (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) (j k : Fin 3) :
    ∫ n : sphere (0 : E3) 1, fderiv ℝ F (r • (n : E3)) (r • angular j k n) ∂sphereMeasure =
      0 :=
  integral_fderiv_angular hW hF hr j k

example (V : Fin 3 → E3 → ℝ) (R : ℝ) :
    ℝ :=
  flux V R

example (V : Fin 3 → E3 → ℝ) (x : E3) :
    ℝ :=
  divergence V x

example (V : Fin 3 → E3 → ℝ) :
    flux V 0 = 0 :=
  flux_zero V

example {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W) (hV : ∀ α, ContDiffOn ℝ 1 (V α) W)
    {r : ℝ} (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    HasDerivAt (flux V) (∫ n : sphere (0 : E3) 1, (2 * r * ∑ α, V α (r • (n : E3)) * (n : E3) α +
      r ^ 2 * ∑ α, fderiv ℝ (V α) (r • (n : E3)) n * (n : E3) α) ∂sphereMeasure) r :=
  hasDerivAt_flux hW hV hr

example (r : ℝ) (n V : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) (hn : ∑ α, n α ^ 2 = 1) :
    2 * r * ∑ α, V α * n α + r ^ 2 * ∑ α, (∑ i, n i * D i α) * n α =
      r ^ 2 * ∑ α, D α α - ∑ j, ∑ k, (r * n j * (r * (n j * D k k - n k * D j k)) +
        V k * (r * (n j * (if j = k then 1 else 0) - n k))) :=
  flux_algebra r n V D hn

example (n : sphere (0 : E3) 1) :
    ∑ α, (n : E3) α ^ 2 = 1 :=
  sum_sq_of_mem_sphere n

example (v : E3) :
    v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) :=
  eq_sum_single v

example (G : E3 → ℝ) (x v : E3) :
    fderiv ℝ G x v = ∑ i, v i * fderiv ℝ G x (EuclideanSpace.single i 1) :=
  fderiv_apply_eq_sum G x v

example {G : E3 → ℝ} {x : E3} (hG : DifferentiableAt ℝ G x) (j : Fin 3) (v : E3) :
    fderiv ℝ (fun y : E3 => y j * G y) x v = x j * fderiv ℝ G x v + G x * v j :=
  fderiv_coord_mul hG j v

example {G : E3 → ℝ} {W : Set E3} (hG : ContDiffOn ℝ 1 G W) (j : Fin 3) :
    ContDiffOn ℝ 1 (fun y : E3 => y j * G y) W :=
  contDiffOn_coord_mul hG j

example {G : E3 → ℝ} {W : Set E3} (hW : IsOpen W) (hG : ContDiffOn ℝ 1 G W) {r : ℝ}
    (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) {u : E3 → E3} (hu : Continuous u) :
    Continuous fun n : sphere (0 : E3) 1 => fderiv ℝ G (r • (n : E3)) (u n) :=
  continuous_fderiv_sphere hW hG hr hu

example {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W) (hV : ∀ α, ContDiffOn ℝ 1 (V α) W) :
    ContinuousOn (divergence V) W :=
  continuousOn_divergence hW hV

example {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W) (hV : ∀ α, ContDiffOn ℝ 1 (V α) W)
    {r : ℝ} (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    HasDerivAt (flux V)
      (r ^ 2 * ∫ n : sphere (0 : E3) 1, divergence V (r • (n : E3)) ∂sphereMeasure) r :=
  hasDerivAt_flux_eq hW hV hr

example {F : E3 → ℝ} (hF : Integrable F) :
    ∫ x, F x = ∫ r in Ioi (0 : ℝ),
      r ^ 2 * ∫ n : sphere (0 : E3) 1, F (r • (n : E3)) ∂sphereMeasure :=
  integral_eq_integral_Ioi_sphere hF

example (R₁ R₂ : ℝ) :
    Set E3 :=
  shell R₁ R₂

example (R₁ R₂ : ℝ) :
    MeasurableSet (shell R₁ R₂) :=
  measurableSet_shell R₁ R₂

example {R₁ R₂ r : ℝ} (hr : 0 ≤ r) (n : sphere (0 : E3) 1) :
    r • (n : E3) ∈ shell R₁ R₂ ↔ r ∈ Ioo R₁ R₂ :=
  smul_mem_shell hr n

example {G : E3 → ℝ} {W : Set E3} (hG : ContinuousOn G W) {R₁ R₂ : ℝ}
    (hsub : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → x ∈ W) :
    IntegrableOn G (shell R₁ R₂) :=
  integrableOn_shell hG hsub

example {V : Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W) (hV : ∀ α, ContDiffOn ℝ 1 (V α) W)
    {R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂) (hsub : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → x ∈ W) :
    flux V R₂ - flux V R₁ = ∫ x in shell R₁ R₂, divergence V x :=
  flux_sub_flux hW hV h0 h12 hsub

example {A : Fin 3 → Fin 3 → E3 → ℝ} {W : Set E3} (hW : IsOpen W)
    (hA : ∀ α β, ContDiffOn ℝ 1 (A α β) W) (hanti : ∀ x ∈ W, ∀ α β, A α β x = -A β α x) {r : ℝ}
    (hr0 : r ≠ 0) (hr : ∀ n ∈ sphere (0 : E3) 1, r • n ∈ W) :
    ∫ n : sphere (0 : E3) 1, ∑ α, ∑ β, fderiv ℝ (A α β) (r • (n : E3))
      (EuclideanSpace.single β 1) * (n : E3) α ∂sphereMeasure = 0 :=
  integral_divergence_antisymm hW hA hanti hr0 hr

end ProjectAinos.SmoothGeometry.Sphere

namespace ProjectAinos.SmoothGeometry

open TopologicalSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Minkowski

example (s : ℝ) (y : E3) :
    HasDerivAt (fun s : ℝ => vector s y) (Pi.single 0 1 : MinkowskiModel 3) s :=
  hasDerivAt_vector_time s y

example (t : ℝ) (y : E3) :
    HasFDerivAt (fun y : E3 => vector t y)
      ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] MinkowskiModel 3).comp
        (ContinuousLinearMap.inr ℝ ℝ E3)) y :=
  hasFDerivAt_vector_space t y

example (α : Fin 3) :
    vector 0 (EuclideanSpace.single α 1) = (Pi.single α.succ 1 : MinkowskiModel 3) :=
  vector_zero_single α

example {f : MinkowskiModel 3 → ℝ} {t : ℝ} {y : E3} (hf : DifferentiableAt ℝ f (vector t y))
    (v : E3) :
    fderiv ℝ (fun y : E3 => f (vector t y)) y v = fderiv ℝ f (vector t y) (vector 0 v) :=
  fderiv_comp_vector hf v

example {f : MinkowskiModel 3 → ℝ} {t : ℝ} {y : E3} (hf : DifferentiableAt ℝ f (vector t y))
    (α : Fin 3) :
    fderiv ℝ (fun y : E3 => f (vector t y)) y (EuclideanSpace.single α 1) =
      fderiv ℝ f (vector t y) (Pi.single α.succ 1) :=
  fderiv_comp_vector_single hf α

example (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : E3 => vector t y) :=
  contDiff_vector_space t

example {U : Set (MinkowskiModel 3)} (hU : IsOpen U) (t : ℝ) :
    IsOpen {y : E3 | vector t y ∈ U} :=
  isOpen_slice hU t

end Minkowski

namespace CoordinateMetric

open Minkowski

section General

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

example (z : MinkowskiModel d) (i k : Fin (d + 1)) :
    g.superpotential z i k k = 0 :=
  superpotential_self g z i k

example (z : MinkowskiModel d) (i k : Fin (d + 1)) :
    ℝ :=
  totalDensity g z i k

example {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      2 * g.totalDensity z i k :=
  sum_fderiv_superpotential g hz i k

example {κ : ℝ} {T : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {z : MinkowskiModel d}
    (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.totalDensity z i k = densityOf g.coefficient z ^ 2 * (κ * T z i k + g.pseudotensor z i k) :=
  totalDensity_eq g hT hz i k

example (i k : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.totalDensity z i k) U :=
  contDiffOn_totalDensity g i k

end General

variable {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric σ 3 U)

example (t : ℝ) (i : Fin 4) (α : Fin 3) (x : E3) :
    ℝ :=
  chargeField g t i α x

example (t R : ℝ) (i : Fin 4) :
    ℝ :=
  surfaceCharge g t R i

example (t : ℝ) (i : Fin 4) (α : Fin 3) (x : E3) :
    ℝ :=
  totalFluxField g t i α x

example (t R : ℝ) (i : Fin 4) :
    ℝ :=
  totalFlux g t R i

example (t : ℝ) (i : Fin 4) (α : Fin 3) :
    ContDiffOn ℝ ∞ (g.chargeField t i α) {y : E3 | vector t y ∈ U} :=
  contDiffOn_chargeField g t i α

example {t : ℝ} {x : E3} (hx : vector t x ∈ U) (i : Fin 4) :
    Sphere.divergence (g.chargeField t i) x = 2 * g.totalDensity (vector t x) i 0 :=
  divergence_chargeField g hx i

example {t R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂)
    (hU : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t R₂ i - g.surfaceCharge t R₁ i =
      ∫ x in Sphere.shell R₁ R₂, g.totalDensity (vector t x) i 0 :=
  surfaceCharge_sub_surfaceCharge g h0 h12 hU i

example {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₁ R₂ : ℝ} (h0 : 0 ≤ R₁)
    (h12 : R₁ ≤ R₂) (hU : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t R₂ i - g.surfaceCharge t R₁ i =
      ∫ x in Sphere.shell R₁ R₂, densityOf g.coefficient (vector t x) ^ 2 *
        (κ * T (vector t x) i 0 + g.pseudotensor (vector t x) i 0) :=
  surfaceCharge_sub_surfaceCharge_eq g hT h0 h12 hU i

example (t : ℝ) (i : Fin 4) :
    g.surfaceCharge t 0 i = 0 :=
  surfaceCharge_zero g t i

example (R : ℝ) :
    Sphere.shell 0 R =ᵐ[volume] ball (0 : E3) R :=
  _root_.ProjectAinos.SmoothGeometry.Sphere.shell_zero_ae_eq R

example {t R : ℝ} (hR : 0 ≤ R) (hU : ∀ x : E3, ‖x‖ ≤ R → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t R i = ∫ x in ball (0 : E3) R, g.totalDensity (vector t x) i 0 :=
  surfaceCharge_eq_integral_ball g hR hU i

example (R : ℝ) :
    Continuous fun p : ℝ × E3 => vector p.1 (R • p.2) :=
  _root_.ProjectAinos.SmoothGeometry.Minkowski.continuous_vector_smul R

example {t R : ℝ} (hR : 0 < R) (hU : ∀ x : E3, ‖x‖ = R → vector t x ∈ U) (i : Fin 4) :
    ContinuousAt (fun s => g.totalFlux s R i) t :=
  continuousAt_totalFlux g hR hU i

example {t R : ℝ} (hR : 0 < R) (hU : ∀ x : E3, ‖x‖ = R → vector t x ∈ U) (i : Fin 4) :
    HasDerivAt (fun s => g.surfaceCharge s R i) (-g.totalFlux t R i) t :=
  hasDerivAt_surfaceCharge_time g hR hU i

example {t₁ t₂ R : ℝ} (ht : t₁ ≤ t₂) (hR : 0 < R)
    (hU : ∀ t ∈ Icc t₁ t₂, ∀ x : E3, ‖x‖ = R → vector t x ∈ U) (i : Fin 4) :
    g.surfaceCharge t₂ R i - g.surfaceCharge t₁ R i =
      -∫ t in t₁..t₂, g.totalFlux t R i :=
  surfaceCharge_sub_surfaceCharge_time g ht hR hU i

end CoordinateMetric

example {n : ℕ} {f : Fin n → ℝ} {c : ℝ} (h : ∀ a, |f a| ≤ c) :
    |∑ a, f a| ≤ n * c :=
  abs_sum_fin_le h

example {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B :=
  abs_mul_le_mul_of_le ha hb

example {n : ℕ} {G : Fin n → Fin n → ℝ} {Γ : Fin n → Fin n → Fin n → ℝ} {K B : ℝ}
    (hG : ∀ a b, |G a b| ≤ K) (hΓ : ∀ a b c, |Γ a b c| ≤ B) (i k : Fin n) :
    |pseudoBraces G Γ i k| ≤ 18 * n ^ 4 * K ^ 2 * B ^ 2 :=
  abs_pseudoBraces_le hG hΓ i k

end ProjectAinos.SmoothGeometry

end PF

section AC

open MeasureTheory Set Metric Real Filter TopologicalSpace

open scoped Topology ContDiff Matrix

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric SmoothGeometry.Minkowski

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}

example (σ : LorentzConvention) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  minkowskiCoefficient σ

example (g : CoordinateMetric σ 3 U) (R₀ C : ℝ) :
    Prop :=
  IsAsymptoticallyGalilean g R₀ C

example (σ : LorentzConvention) (a : Fin 4) :
    |lorentzSign σ a| = 1 :=
  abs_lorentzSign σ a

example (σ : LorentzConvention) (a b : Fin 4) :
    |minkowskiCoefficient σ a b| ≤ 1 :=
  abs_minkowskiCoefficient_le σ a b

example {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : ∀ a b, |M a b - minkowskiCoefficient σ a b| ≤ 1 / 8) :
    M.det ≠ 0 ∧ (∀ a b, |M⁻¹ a b| ≤ 2) ∧ |M.det| ≤ 384 :=
  inv_bound_of_near_minkowski hM

example (C : ℝ) :
    ℝ :=
  decayConstant C

example (C : ℝ) :
    0 ≤ decayConstant C :=
  decayConstant_nonneg C

namespace IsAsymptoticallyGalileanAt

variable {g : CoordinateMetric σ 3 U} {t R₀ C : ℝ}

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : R₀ ≤ ‖x‖) :
    0 < ‖x‖ :=
  norm_pos h hx

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : max R₀ (8 * C) ≤ ‖x‖)
    (a b : Fin 4) :
    |g.coefficient (vector t x) a b - minkowskiCoefficient σ a b| ≤ 1 / 8 :=
  coefficient_near h hx a b

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : max R₀ (8 * C) ≤ ‖x‖)
    (a b : Fin 4) :
    |(g.coefficient (vector t x))⁻¹ a b| ≤ 2 :=
  abs_inv_le h hx a b

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : max R₀ (8 * C) ≤ ‖x‖) :
    densityOf g.coefficient (vector t x) ^ 2 ≤ 384 :=
  densityOf_sq_le h hx

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : max R₀ (8 * C) ≤ ‖x‖)
    (k i j : Fin 4) :
    |christoffelOf g.coefficient (vector t x) k i j| ≤ 12 * C / ‖x‖ ^ 2 :=
  abs_christoffelOf_le h hx k i j

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : max R₀ (8 * C) ≤ ‖x‖)
    (i k : Fin 4) :
    |g.pseudotensor (vector t x) i k| ≤ 1327104 * C ^ 2 / ‖x‖ ^ 4 :=
  abs_pseudotensor_le h hx i k

example (h : IsAsymptoticallyGalileanAt g t R₀ C) {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {Rm : ℝ} {i k : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → T (vector t x) i k = 0) {x : E3}
    (hx : max (max R₀ (8 * C)) Rm ≤ ‖x‖) :
    |g.totalDensity (vector t x) i k| ≤ decayConstant C / ‖x‖ ^ 4 :=
  abs_totalDensity_le h hT hm hx

end IsAsymptoticallyGalileanAt

example {f : E3 → ℝ} (hf : Continuous f) {R K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : E3, R ≤ ‖x‖ → |f x| ≤ K / ‖x‖ ^ 4) :
    Integrable f :=
  integrable_of_le_div_pow_four hf hK0 hK

example {g : CoordinateMetric σ 3 U} {t : ℝ} (hU : ∀ x : E3, vector t x ∈ U) (i k : Fin 4) :
    Continuous fun x : E3 => g.totalDensity (vector t x) i k :=
  continuous_totalDensity_slice hU i k

example {g : CoordinateMetric σ 3 U} {t : ℝ} (hU : ∀ x : E3, vector t x ∈ U) {i : Fin 4}
    (hint : Integrable fun x : E3 => g.totalDensity (vector t x) i 0) :
    Tendsto (fun R => g.surfaceCharge t R i) atTop
      (𝓝 (∫ x : E3, g.totalDensity (vector t x) i 0)) :=
  tendsto_surfaceCharge_of_integrable hU hint

example (g : CoordinateMetric σ 3 U) (t : ℝ) (i : Fin 4) :
    ℝ :=
  charge g t i

example {g : CoordinateMetric σ 3 U} {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₀ C Rm : ℝ}
    (hg : IsAsymptoticallyGalileanAt g t R₀ C) (hU : ∀ x : E3, vector t x ∈ U) {i : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → T (vector t x) i 0 = 0) :
    Tendsto (fun R => g.surfaceCharge t R i) atTop
      (𝓝 (∫ x : E3, densityOf g.coefficient (vector t x) ^ 2 *
        (κ * T (vector t x) i 0 + g.pseudotensor (vector t x) i 0))) :=
  tendsto_surfaceCharge hT hg hU hm

example {g : CoordinateMetric σ 3 U} {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₀ C Rm : ℝ}
    (hg : IsAsymptoticallyGalileanAt g t R₀ C) (hU : ∀ x : E3, vector t x ∈ U) {i : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → T (vector t x) i 0 = 0) :
    charge g t i = ∫ x : E3, densityOf g.coefficient (vector t x) ^ 2 *
      (κ * T (vector t x) i 0 + g.pseudotensor (vector t x) i 0) :=
  charge_eq_integral hT hg hU hm

example {g : CoordinateMetric σ 3 U} {t₁ t₂ R₀ : ℝ} (ht : t₁ ≤ t₂) (hR₀ : 0 < R₀)
    (hU : ∀ t ∈ Icc t₁ t₂, ∀ x : E3, R₀ ≤ ‖x‖ → vector t x ∈ U) {i : Fin 4} {P₁ P₂ : ℝ}
    (h₁ : Tendsto (fun R => g.surfaceCharge t₁ R i) atTop (𝓝 P₁))
    (h₂ : Tendsto (fun R => g.surfaceCharge t₂ R i) atTop (𝓝 P₂))
    (hflux : ∀ ε > 0, ∀ᶠ R in atTop, ∀ t ∈ Icc t₁ t₂, |g.totalFlux t R i| ≤ ε) :
    P₁ = P₂ :=
  charge_const_of_flux ht hR₀ hU h₁ h₂ hflux

example {g : CoordinateMetric σ 3 U} {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₀ C Rm R : ℝ}
    (hg : IsAsymptoticallyGalileanAt g t R₀ C) {i : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → ∀ k, T (vector t x) i k = 0) (hR : max (max R₀ (8 * C)) Rm ≤ R) :
    |g.totalFlux t R i| ≤ 12 * π * decayConstant C / R ^ 2 :=
  abs_totalFlux_le hT hg hm hR

example {g : CoordinateMetric σ 3 U} {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t₁ t₂ R₀ C Rm : ℝ} (ht : t₁ ≤ t₂)
    (hg : ∀ t ∈ Icc t₁ t₂, IsAsymptoticallyGalileanAt g t R₀ C) (hU₁ : ∀ x : E3, vector t₁ x ∈ U)
    (hU₂ : ∀ x : E3, vector t₂ x ∈ U) {i : Fin 4}
    (hm : ∀ t ∈ Icc t₁ t₂, ∀ x : E3, Rm ≤ ‖x‖ → ∀ k, T (vector t x) i k = 0) :
    ∫ x : E3, densityOf g.coefficient (vector t₁ x) ^ 2 *
        (κ * T (vector t₁ x) i 0 + g.pseudotensor (vector t₁ x) i 0) =
      ∫ x : E3, densityOf g.coefficient (vector t₂ x) ^ 2 *
        (κ * T (vector t₂ x) i 0 + g.pseudotensor (vector t₂ x) i 0) :=
  charge_const hT ht hg hU₁ hU₂ hm

example (R₀ : ℝ) (x : E3) :
    ℝ :=
  isotropicProfile R₀ x

example {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ContDiff ℝ ∞ (isotropicProfile R₀) :=
  contDiff_isotropicProfile hR₀

example (R₀ : ℝ) (x : E3) :
    0 ≤ isotropicProfile R₀ x :=
  isotropicProfile_nonneg R₀ x

example {R₀ : ℝ} (hR₀ : 0 < R₀) (x : E3) :
    isotropicProfile R₀ x ≤ R₀⁻¹ :=
  isotropicProfile_le hR₀ x

example {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ ≤ ‖x‖) :
    isotropicProfile R₀ x = ‖x‖⁻¹ :=
  isotropicProfile_eq hR₀ hx

example {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) :
    isotropicProfile R₀ =ᶠ[𝓝 x] fun y => ‖y‖⁻¹ :=
  isotropicProfile_eventuallyEq hR₀ hx

example {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E3 => ‖y‖⁻¹) (-(‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x :=
  hasFDerivAt_norm_inv hx

example {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (u : E3) :
    fderiv ℝ (isotropicProfile R₀) x u = -(inner ℝ x u / ‖x‖ ^ 3) :=
  fderiv_isotropicProfile hR₀ hx u

example {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x v =
      -(inner ℝ v u / ‖x‖ ^ 3) + 3 * inner ℝ x u * inner ℝ x v / ‖x‖ ^ 5 :=
  fderiv_fderiv_isotropicProfile hR₀ hx u v

example (σ : LorentzConvention) (M R₀ : ℝ) (z : MinkowskiModel 3) (i : Fin 4) :
    ℝ :=
  isotropicCoefficient σ M R₀ z i

example (σ : LorentzConvention) (M R₀ : ℝ) (z : MinkowskiModel 3) :
    isotropicCoefficient σ M R₀ z 0 =
      σ.timeSign * (1 - 2 * M * isotropicProfile R₀ (space z)) :=
  isotropicCoefficient_zero σ M R₀ z

example (σ : LorentzConvention) (M R₀ : ℝ) (z : MinkowskiModel 3) (α : Fin 3) :
    isotropicCoefficient σ M R₀ z α.succ =
      -σ.timeSign * (1 + 2 * M * isotropicProfile R₀ (space z)) :=
  isotropicCoefficient_succ σ M R₀ z α

example {R₀ : ℝ} (hR₀ : 0 < R₀) (z : MinkowskiModel 3) :
    HasFDerivAt (fun w : MinkowskiModel 3 => isotropicProfile R₀ (space w))
      ((fderiv ℝ (isotropicProfile R₀) (space z)).comp space) z :=
  hasFDerivAt_isotropicProfile_space hR₀ z

example (σ : LorentzConvention) (M : ℝ) {R₀ : ℝ} (hR₀ : 0 < R₀) (i : Fin 4) :
    ContDiff ℝ ∞ fun z => isotropicCoefficient σ M R₀ z i :=
  contDiff_isotropicCoefficient σ M hR₀ i

example (σ : LorentzConvention) (M : ℝ) {R₀ : ℝ} (hR₀ : 0 < R₀) (z v : MinkowskiModel 3)
    (i : Fin 4) :
    fderiv ℝ (fun w => isotropicCoefficient σ M R₀ w i) z v =
      -σ.timeSign * (2 * M * fderiv ℝ (isotropicProfile R₀) (space z) (space v)) :=
  fderiv_isotropicCoefficient σ M hR₀ z v i

example {M R₀ : ℝ} (hM : 0 ≤ M) (hR : 2 * M < R₀) (x : E3) :
    0 ≤ 2 * M * isotropicProfile R₀ x ∧ 2 * M * isotropicProfile R₀ x < 1 :=
  isotropic_bounds hM hR x

example (σ : LorentzConvention) (M R₀ : ℝ) (hM : 0 ≤ M) (hR : 2 * M < R₀) :
    CoordinateMetric σ 3 ⊤ :=
  isotropicMetric σ M R₀ hM hR

variable {M R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}

example (z : MinkowskiModel 3) :
    (isotropicMetric σ M R₀ hM hR).coefficient z =
      Matrix.diagonal (isotropicCoefficient σ M R₀ z) :=
  coefficient_isotropicMetric z

example (c : Fin 4) :
    ‖space (Pi.single c 1 : MinkowskiModel 3)‖ ≤ 1 :=
  norm_space_single_le c

example :
    IsAsymptoticallyGalilean (isotropicMetric σ M R₀ hM hR) (3 * R₀) (8 * M) :=
  isAsymptoticallyGalilean_isotropicMetric

example (α : Fin 3) :
    space (Pi.single α.succ 1 : MinkowskiModel 3) = EuclideanSpace.single α 1 :=
  space_single_succ α

example {c : Fin 4 → ℝ} (hc : ∀ i, c i ≠ 0) :
    (Matrix.diagonal c)⁻¹ = Matrix.diagonal fun l => (c l)⁻¹ :=
  inv_diagonal_of_ne_zero hc

example (z : MinkowskiModel 3) (α : Fin 3) (m : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).superpotentialDensity z 0 0 α.succ m =
      if m = α.succ then -(1 + 2 * M * isotropicProfile R₀ (space z)) ^ 2 else 0 :=
  superpotentialDensity_isotropicMetric z α m

example (z : MinkowskiModel 3) (α : Fin 3) :
    (isotropicMetric σ M R₀ hM hR).superpotential z 0 0 α.succ =
      -(2 * (1 + 2 * M * isotropicProfile R₀ (space z)) *
        (2 * M * fderiv ℝ (isotropicProfile R₀) (space z) (EuclideanSpace.single α 1))) :=
  superpotential_isotropicMetric z α

example (t : ℝ) {R : ℝ} (hRR : 2 * R₀ < R) :
    (isotropicMetric σ M R₀ hM hR).surfaceCharge t R 0 = 8 * π * M * (1 + 2 * M / R) :=
  surfaceCharge_isotropicMetric t hRR

example (t : ℝ) :
    Tendsto (fun R => (isotropicMetric σ M R₀ hM hR).surfaceCharge t R 0) atTop
      (𝓝 (8 * π * M)) :=
  tendsto_surfaceCharge_isotropicMetric t

example (t : ℝ) :
    charge (isotropicMetric σ M R₀ hM hR) t 0 = 8 * π * M :=
  charge_zero_eq_mass t

example (z : MinkowskiModel 3) :
    (CoordinateMetric.minkowski σ 3 U).coefficient z = minkowskiCoefficient σ :=
  coefficient_minkowski z

example (σ : LorentzConvention) :
    IsAsymptoticallyGalilean (CoordinateMetric.minkowski σ 3 ⊤) 1 0 :=
  isAsymptoticallyGalilean_minkowski σ

example {z : MinkowskiModel 3} (hz : z ∈ U) (i k : Fin 4) :
    (CoordinateMetric.minkowski σ 3 U).raisedEinstein z i k = 0 :=
  raisedEinstein_minkowski hz i k

example {z : MinkowskiModel 3} (hz : z ∈ U) (i k : Fin 4) :
    (CoordinateMetric.minkowski σ 3 U).pseudotensor z i k = 0 :=
  pseudotensor_minkowski hz i k

example (σ : LorentzConvention) (t : ℝ) (i : Fin 4) :
    Tendsto (fun R => (CoordinateMetric.minkowski σ 3 ⊤).surfaceCharge t R i) atTop (𝓝 0) :=
  tendsto_surfaceCharge_minkowski σ t i

example (σ : LorentzConvention) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (i : Fin 4) :
    ∫ x : E3, densityOf (CoordinateMetric.minkowski σ 3 ⊤).coefficient (vector t₁ x) ^ 2 *
        (1 * 0 + (CoordinateMetric.minkowski σ 3 ⊤).pseudotensor (vector t₁ x) i 0) =
      ∫ x : E3, densityOf (CoordinateMetric.minkowski σ 3 ⊤).coefficient (vector t₂ x) ^ 2 *
        (1 * 0 + (CoordinateMetric.minkowski σ 3 ⊤).pseudotensor (vector t₂ x) i 0) :=
  charge_const_minkowski σ ht i

end ProjectAinos.GeneralRelativity

end AC

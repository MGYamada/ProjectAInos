/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateKilling
import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFrameCriterion

/-! Public consumers of the co-ordinate tools of wave F14: metrics with diagonal coefficients and
their Christoffel symbols, the Ricci and curvature tensors of a certified table of Christoffel
symbols, the geodesic equation of a coordinate metric in its co-ordinates, Killing fields given by
their components, and the Lorentz criterion for a form in a pointwise frame, with their regression
examples. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

section DiagonalMetric


open ContinuousLinearMap Set TopologicalSpace

open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (x : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  diagonalForm c x

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (x v w : MinkowskiModel d) :
    diagonalForm c x v w = ∑ i, c x i * v i * w i :=
  diagonalForm_apply c x v w

example {c : MinkowskiModel d → Fin (d + 1) → ℝ} (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U) :
    ContDiffOn ℝ ∞ (diagonalForm c) U :=
  contDiffOn_diagonalForm hc

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) :
    CoordinateMetric σ d U :=
  ofDiagonal c hc h0 hs

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) :
    (ofDiagonal c hc h0 hs).form = diagonalForm c :=
  ofDiagonal_form c hc h0 hs

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) (y : MinkowskiModel d) :
    (ofDiagonal c hc h0 hs).coefficient y = Matrix.diagonal (c y) :=
  coefficient_ofDiagonal c hc h0 hs y

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (y v : MinkowskiModel d) (i j : Fin (d + 1)) :
    fderiv ℝ (fun z => Matrix.diagonal (c z) i j) y v =
      if i = j then fderiv ℝ (fun z => c z i) y v else 0 :=
  fderiv_diagonal_apply c y v i j

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (y : MinkowskiModel d) (hy : ∀ i, c y i ≠ 0)
    (k i j : Fin (d + 1)) :
    christoffelOf (fun z => Matrix.diagonal (c z)) y k i j =
      ((if k = j then fderiv ℝ (fun z => c z k) y (Pi.single i 1) else 0) +
        (if k = i then fderiv ℝ (fun z => c z k) y (Pi.single j 1) else 0) -
        (if i = j then fderiv ℝ (fun z => c z i) y (Pi.single k 1) else 0)) / (2 * c y k) :=
  christoffelOf_diagonal c y hy k i j

example (c : MinkowskiModel d → Fin (d + 1) → ℝ) (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) (y : MinkowskiModel d)
    (hy : ∀ i, c y i ≠ 0) (k i j : Fin (d + 1)) :
    christoffelOf (ofDiagonal c hc h0 hs).coefficient y k i j =
      ((if k = j then fderiv ℝ (fun z => c z k) y (Pi.single i 1) else 0) +
        (if k = i then fderiv ℝ (fun z => c z k) y (Pi.single j 1) else 0) -
        (if i = j then fderiv ℝ (fun z => c z i) y (Pi.single k 1) else 0)) / (2 * c y k) :=
  christoffelOf_ofDiagonal c hc h0 hs y hy k i j

example (σ : LorentzConvention) :
    -σ.timeSign * lorentzSign σ (0 : Fin (d + 1)) < 0 :=
  lorentzSign_time_neg σ

example (σ : LorentzConvention) (α : Fin d) :
    0 < -σ.timeSign * lorentzSign σ α.succ :=
  lorentzSign_space_pos σ α

example (σ : LorentzConvention) (d : ℕ) (U : Opens (MinkowskiModel d)) :
    minkowski σ d U = ofDiagonal (fun _ => lorentzSign σ) (fun _ => contDiffOn_const)
      (fun _ _ => lorentzSign_time_neg σ) (fun _ _ α => lorentzSign_space_pos σ α) :=
  minkowski_eq_ofDiagonal σ d U

example (y : MinkowskiModel d) (k i j : Fin (d + 1)) :
    christoffelOf (minkowski σ d U).coefficient y k i j = 0 :=
  christoffelOf_minkowski y k i j

example (x : MinkowskiModel 1) :
    Fin 2 → ℝ :=
  diagonalExample x

example (x : MinkowskiModel 1) :
    diagonalExample x 0 = -(1 + x 1 ^ 2) :=
  diagonalExample_zero x

example (x : MinkowskiModel 1) :
    diagonalExample x 1 = 1 :=
  diagonalExample_one x

example (x : MinkowskiModel 1) (i : Fin 2) :
    diagonalExample x i ≠ 0 :=
  diagonalExample_ne_zero x i

example :
    CoordinateMetric .timeNegative 1 ⊤ :=
  diagonalExampleMetric

example (y : MinkowskiModel 1) :
    christoffelOf diagonalExampleMetric.coefficient y 1 0 0 = y 1 :=
  christoffelOf_diagonalExampleMetric y

end ProjectAinos.SmoothGeometry.CoordinateMetric

end DiagonalMetric

section ChristoffelCertificate


open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric Matrix

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

example (G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (y : MinkowskiModel d) (j k : Fin (d + 1)) :
    ℝ :=
  ricciOfChristoffel G y j k

example (G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (y : MinkowskiModel d) (l i j k : Fin (d + 1)) :
    ℝ :=
  curvatureOf G y l i j k

example (G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (y : MinkowskiModel d) (j k : Fin (d + 1)) :
    ricciOfChristoffel G y j k = ∑ i, curvatureOf G y i i j k :=
  ricciOfChristoffel_eq_sum_curvatureOf G y j k

example {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {y : MinkowskiModel d}
    (hG : ∀ᶠ z in 𝓝 y, ∀ k i j, christoffelOf C z k i j = G z k i j) (j k : Fin (d + 1)) :
    ricciOf C y j k = ricciOfChristoffel G y j k :=
  ricciOf_eq_ricciOfChristoffel hG j k

example {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U) (x y : U)
    {G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hG : ∀ᶠ z in 𝓝 (y : MinkowskiModel d), ∀ k i j,
      christoffelOf g.coefficient z k i j = G z k i j)
    (l i j k : Fin (d + 1)) :
    g.toLorentzMetric.chartCurvature (physicalChart x) y l i j k = curvatureOf G y l i j k :=
  toLorentzMetric_chartCurvature_eq_curvatureOf g x y hG l i j k

example {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U) {z : MinkowskiModel d}
    (hz : z ∈ U) (Γ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (hΓ : ∀ l i j, ∑ q, g.coefficient z l q * Γ q i j =
      (fderiv ℝ (fun w => g.coefficient w j l) z (Pi.single i 1) +
        fderiv ℝ (fun w => g.coefficient w l i) z (Pi.single j 1) -
        fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single l 1)) / 2)
    (k i j : Fin (d + 1)) :
    christoffelOf g.coefficient z k i j = Γ k i j :=
  christoffelOf_eq_of_lowered g hz Γ hΓ k i j

example {f : MinkowskiModel d → ℝ} {y : MinkowskiModel d} (hf : DifferentiableAt ℝ f y)
    (i : Fin (d + 1)) :
    fderiv ℝ f y (Pi.single i 1) = deriv (fun s => f (Function.update y i s)) (y i) :=
  fderiv_single_eq_deriv_update hf i

example {U : Opens (MinkowskiModel d)} {z : MinkowskiModel d} (hz : z ∈ U) (k i j : Fin (d + 1)) :
    christoffelOf (minkowski σ d U).coefficient z k i j = 0 :=
  minkowski_christoffelOf hz k i j

example {U : Opens (MinkowskiModel d)} {z : MinkowskiModel d} (hz : z ∈ U) (j k : Fin (d + 1)) :
    ricciOf (minkowski σ d U).coefficient z j k = 0 :=
  minkowski_ricciOf hz j k

namespace DeSitterPlane

example (q : MinkowskiModel 1) :
    MinkowskiModel 1 →L[ℝ] MinkowskiModel 1 →L[ℝ] ℝ :=
  form q

example (q v w : MinkowskiModel 1) :
    form q v w = -(v 0 * w 0) + Real.exp (2 * q 0) * (v 1 * w 1) :=
  form_apply q v w

example :
    ContDiff ℝ ∞ form :=
  contDiff_form

example :
    CoordinateMetric .timeNegative 1 ⊤ :=
  metric

example (q : MinkowskiModel 1) (a b : Fin 2) :
    metric.coefficient q a b = form q (Pi.single a 1) (Pi.single b 1) :=
  coefficient_apply q a b

example (q : MinkowskiModel 1) :
    Fin 2 → Fin 2 → Fin 2 → ℝ :=
  christoffel q

example (q v : MinkowskiModel 1) :
    fderiv ℝ (fun w : MinkowskiModel 1 => Real.exp (2 * w 0)) q v =
      2 * Real.exp (2 * q 0) * v 0 :=
  fderiv_exp q v

example (z : MinkowskiModel 1) (k i j : Fin 2) :
    christoffelOf metric.coefficient z k i j = christoffel z k i j :=
  christoffelOf_eq z k i j

example (q : MinkowskiModel 1) (j k : Fin 2) :
    ricciOf metric.coefficient q j k = metric.coefficient q j k :=
  ricciOf_eq q j k

example (x y : (⊤ : Opens (MinkowskiModel 1))) (j k : Fin 2) :
    metric.toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = metric.coefficient y j k :=
  ricci_chartField x y j k

end DeSitterPlane

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end ChristoffelCertificate

section CoordinateGeodesic


open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → U} {p₀ : F} :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) f p₀ ↔
      DifferentiableAt ℝ (fun p => (f p : MinkowskiModel d)) p₀ :=
  mdifferentiableAt_iff_differentiableAt_val

variable (g : CoordinateMetric σ d U)

example {γ : ℝ → U} {t : ℝ} (hγ : ContDiffAt ℝ 2 (fun t => (γ t : MinkowskiModel d)) t) :
    g.toLorentzMetric.covariantAlong (curveVelocity γ) t = 0 ↔ ∀ k : Fin (d + 1),
      deriv (deriv (fun t => (γ t : MinkowskiModel d))) t k +
        ∑ i, ∑ j, christoffelOf g.coefficient (γ t) k i j *
          deriv (fun t => (γ t : MinkowskiModel d)) t i *
            deriv (fun t => (γ t : MinkowskiModel d)) t j = 0 :=
  covariantAlong_curveVelocity_eq_zero_iff g hγ

example {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s)
    (hγ : ContDiffOn ℝ 2 (fun t => (γ t : MinkowskiModel d)) s) :
    g.toLorentzMetric.IsGeodesicOn s γ ↔ ∀ t ∈ s, ∀ k : Fin (d + 1),
      deriv (deriv (fun t => (γ t : MinkowskiModel d))) t k +
        ∑ i, ∑ j, christoffelOf g.coefficient (γ t) k i j *
          deriv (fun t => (γ t : MinkowskiModel d)) t i *
            deriv (fun t => (γ t : MinkowskiModel d)) t j = 0 :=
  isGeodesicOn_iff g hs hγ

example {γ : ℝ → U} {t : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel d)) t) :
    g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * deriv (fun t => (γ t : MinkowskiModel d)) t i *
        deriv (fun t => (γ t : MinkowskiModel d)) t j :=
  form_curveVelocity g hγ

example {γ : ℝ → U} {t : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel d)) t)
    (x : U) (v : MinkowskiModel d) :
    g.toLorentzMetric.form (γ t) (chartField (physicalChart x) v (γ t)) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * v i *
        deriv (fun t => (γ t : MinkowskiModel d)) t j :=
  pairing_curveVelocity g hγ x v

example {γ : ℝ → U} {s : Set ℝ} (hs : IsOpen s) (a b : MinkowskiModel d)
    (hγ : ∀ t ∈ s, (γ t : MinkowskiModel d) = a + t • b) :
    (minkowski σ d U).toLorentzMetric.IsGeodesicOn s γ :=
  minkowski_isGeodesicOn_line hs a b hγ

end ProjectAinos.SmoothGeometry.CoordinateMetric

end CoordinateGeodesic

section CoordinateKilling


open Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)}

example (x₀ : U) (ξ : MinkowskiModel d → MinkowskiModel d) :
    ∀ y : U, TangentSpace 𝓘(ℝ, MinkowskiModel d) y :=
  vectorFieldOf x₀ ξ

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (ξ : MinkowskiModel d → MinkowskiModel d) (y : MinkowskiModel d) (i j : Fin (d + 1)) :
    ℝ :=
  lieOf C ξ y i j

example (x₀ y : U) (ξ : MinkowskiModel d → MinkowskiModel d) :
    (vectorFieldOf x₀ ξ y : MinkowskiModel d) = ξ y :=
  vectorFieldOf_apply x₀ y ξ

example (x₀ : U) (v : MinkowskiModel d) :
    vectorFieldOf x₀ (fun _ => v) = chartField (physicalChart x₀) v :=
  vectorFieldOf_const x₀ v

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (v y : MinkowskiModel d)
    (i j : Fin (d + 1)) :
    lieOf C (fun _ => v) y i j = fderiv ℝ (fun z => C z i j) y v :=
  lieOf_const C v y i j

example {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) :
    ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ (fun z : U => ξ z) :=
  contMDiff_components hξ

example {ξ : MinkowskiModel d → MinkowskiModel d} (hξ : ContDiffOn ℝ ∞ ξ U) (x₀ y : U)
    (v : MinkowskiModel d) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun z : U => ξ z) y (chartField (physicalChart x₀) v y) =
      fderiv ℝ ξ y v :=
  mvfderiv_components hξ x₀ y v

example (g : CoordinateMetric σ d U) (x₀ y : U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (v : MinkowskiModel d) (k : Fin (d + 1)) :
    (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y v : MinkowskiModel d) k =
      fderiv ℝ (fun z => ξ z k) y v +
        ∑ i, ∑ j, christoffelOf g.coefficient y k i j * v i * ξ y j :=
  leviCivita_vectorFieldOf g x₀ y hξ v k

example (g : CoordinateMetric σ d U) {y : MinkowskiModel d} (hy : y ∈ U) (i j : Fin (d + 1))
    (v : MinkowskiModel d) :
    fderiv ℝ (fun z => g.coefficient z i j) y v =
      ∑ b, v b * ∑ l, (christoffelOf g.coefficient y l i b * g.coefficient y l j +
        christoffelOf g.coefficient y l j b * g.coefficient y i l) :=
  fderiv_coefficient_apply g hy i j v

example (g : CoordinateMetric σ d U) (x₀ y : U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (i k : Fin (d + 1)) :
    (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single i 1) : MinkowskiModel d) k =
      fderiv ℝ (fun z => ξ z k) y (Pi.single i 1) +
        ∑ j, christoffelOf g.coefficient y k i j * ξ y j :=
  leviCivita_vectorFieldOf_single g x₀ y hξ i k

example (g : CoordinateMetric σ d U) (y a : MinkowskiModel d) (j : Fin (d + 1)) :
    g.form y a (Pi.single j 1) = ∑ k, g.coefficient y k j * a k :=
  form_single_right g y a j

example (g : CoordinateMetric σ d U) (y b : MinkowskiModel d) (i : Fin (d + 1)) :
    g.form y (Pi.single i 1) b = ∑ k, g.coefficient y i k * b k :=
  form_single_left g y b i

example (g : CoordinateMetric σ d U) (x₀ y : U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (i j : Fin (d + 1)) :
    g.form y (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single i 1))
        (Pi.single j 1) +
      g.form y (Pi.single i 1)
        (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y (Pi.single j 1)) =
      lieOf g.coefficient ξ y i j :=
  killing_vectorFieldOf_single g x₀ y hξ i j

example (g : CoordinateMetric σ d U) (x₀ y : U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    g.toLorentzMetric.form y (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y v) w +
        g.toLorentzMetric.form y v (g.toLorentzMetric.leviCivita (vectorFieldOf x₀ ξ) y w) =
      ∑ i, ∑ j, lieOf g.coefficient ξ y i j * (v : MinkowskiModel d) i *
        (w : MinkowskiModel d) j :=
  killing_vectorFieldOf g x₀ y hξ v w

example (g : CoordinateMetric σ d U) (x₀ : U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) :
    g.toLorentzMetric.IsKillingField (vectorFieldOf x₀ ξ) ↔
      ∀ y ∈ U, ∀ i j, lieOf g.coefficient ξ y i j = 0 :=
  isKillingField_iff_lieOf g x₀ hξ

example (g : CoordinateMetric σ d U) (x₀ : U) {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (h : ∀ y ∈ U, ∀ i j, lieOf g.coefficient ξ y i j = 0) :
    g.toLorentzMetric.IsKillingField (vectorFieldOf x₀ ξ) :=
  isKillingField_of_lieOf g x₀ hξ h

example (g : CoordinateMetric σ d U) (x₀ : U) (v : MinkowskiModel d)
    (h : ∀ y ∈ U, ∀ i j, fderiv ℝ (fun z => g.coefficient z i j) y v = 0) :
    g.toLorentzMetric.IsKillingField (chartField (physicalChart x₀) v) :=
  isKillingField_const g x₀ v h

example (g : CoordinateMetric σ d U) (R : MinkowskiModel d →L[ℝ] MinkowskiModel d)
    (y : MinkowskiModel d) (i j : Fin (d + 1)) :
    lieOf g.coefficient R y i j = fderiv ℝ (fun z => g.coefficient z i j) y (R y) +
      g.form y (R (Pi.single i 1)) (Pi.single j 1) +
      g.form y (Pi.single i 1) (R (Pi.single j 1)) :=
  lieOf_linear g R y i j

example (R : MinkowskiModel d →L[ℝ] MinkowskiModel d)
    (hR : ∀ v w, minkowskiForm σ d (R v) w + minkowskiForm σ d v (R w) = 0) (y : MinkowskiModel d)
    (i j : Fin (d + 1)) :
    lieOf (minkowski σ d U).coefficient R y i j = 0 :=
  lieOf_minkowski_linear R hR y i j

example (x₀ : U) (R : MinkowskiModel d →L[ℝ] MinkowskiModel d)
    (hR : ∀ v w, minkowskiForm σ d (R v) w + minkowskiForm σ d v (R w) = 0) :
    (minkowski σ d U).toLorentzMetric.IsKillingField (vectorFieldOf x₀ R) :=
  isKillingField_minkowski_linear x₀ R hR

example :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  minkowskiRotation

example (x : MinkowskiModel 3) :
    minkowskiRotation x = ![0, -x 2, x 1, 0] :=
  minkowskiRotation_apply x

example (v w : MinkowskiModel 3) :
    minkowskiForm σ 3 (minkowskiRotation v) w + minkowskiForm σ 3 v (minkowskiRotation w) = 0 :=
  minkowskiForm_rotation_add v w

example {U : Opens (MinkowskiModel 3)} (x₀ : U) :
    (minkowski σ 3 U).toLorentzMetric.IsKillingField (vectorFieldOf x₀ minkowskiRotation) :=
  isKillingField_minkowskiRotation x₀

example {U : Opens (MinkowskiModel 3)} (y : MinkowskiModel 3) (i j : Fin 4) :
    lieOf (minkowski σ 3 U).coefficient (fun x => ![0, -x 2, x 1, 0]) y i j = 0 :=
  lieOf_rotation y i j

example {U : Opens (MinkowskiModel 3)} (x₀ : U) :
    (minkowski σ 3 U).toLorentzMetric.IsKillingField
      (vectorFieldOf x₀ fun x => ![0, -x 2, x 1, 0]) :=
  isKillingField_rotation x₀

example :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  minkowskiBoost

example (x : MinkowskiModel 3) :
    minkowskiBoost x = ![x 1, x 0, 0, 0] :=
  minkowskiBoost_apply x

example (v w : MinkowskiModel 3) :
    minkowskiForm σ 3 (minkowskiBoost v) w + minkowskiForm σ 3 v (minkowskiBoost w) = 0 :=
  minkowskiForm_boost_add v w

example {U : Opens (MinkowskiModel 3)} (x₀ : U) :
    (minkowski σ 3 U).toLorentzMetric.IsKillingField
      (vectorFieldOf x₀ fun x => ![x 1, x 0, 0, 0]) :=
  isKillingField_boost x₀

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end CoordinateKilling

section CoordinateFrameCriterion


open ContinuousLinearMap TopologicalSpace

open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (P : MinkowskiModel d → MinkowskiModel d ≃L[ℝ] MinkowskiModel d)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (P x (Fin.cons 1 (0 : Fin d → ℝ))) (P x (Fin.cons 1 (0 : Fin d → ℝ))) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (P x (Fin.cons 0 v)) (P x (Fin.cons 0 v))) :
    CoordinateMetric σ d U :=
  ofFrameCriterion B hB hs P ht hx

example (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (P : MinkowskiModel d → MinkowskiModel d ≃L[ℝ] MinkowskiModel d)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (P x (Fin.cons 1 (0 : Fin d → ℝ))) (P x (Fin.cons 1 (0 : Fin d → ℝ))) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 →
      0 < -σ.timeSign * B x (P x (Fin.cons 0 v)) (P x (Fin.cons 0 v))) :
    (ofFrameCriterion B hB hs P ht hx).form = B :=
  ofFrameCriterion_form B hB hs P ht hx

example (B : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U) (hs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (ht : ∀ x ∈ U, -σ.timeSign *
      B x (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0)
    (hx : ∀ x ∈ U, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < -σ.timeSign * B x (Fin.cons 0 v) (Fin.cons 0 v)) :
    ofFrameCriterion B hB hs (fun _ => ContinuousLinearEquiv.refl ℝ _) ht hx =
      ofCriterion B hB hs ht hx :=
  ofFrameCriterion_refl B hB hs ht hx

example :
    MinkowskiModel 1 →L[ℝ] MinkowskiModel 1 →L[ℝ] ℝ :=
  nullForm

example (v w : MinkowskiModel 1) :
    nullForm v w = v 0 * w 1 + v 1 * w 0 :=
  nullForm_apply v w

example :
    nullForm (Fin.cons 1 (0 : Fin 1 → ℝ)) (Fin.cons 1 (0 : Fin 1 → ℝ)) = 0 :=
  nullForm_timeAxis

example (σ : LorentzConvention) :
    ¬ (-σ.timeSign * nullForm (Fin.cons 1 (0 : Fin 1 → ℝ)) (Fin.cons 1 (0 : Fin 1 → ℝ)) < 0) :=
  not_nullForm_timeAxis_neg σ

example :
    MinkowskiModel 1 ≃ₗ[ℝ] MinkowskiModel 1 :=
  nullFrameLinear

example :
    MinkowskiModel 1 ≃L[ℝ] MinkowskiModel 1 :=
  nullFrame

example (v : MinkowskiModel 1) :
    nullFrame v = ![v 0 + v 1, v 1 - v 0] :=
  nullFrame_apply v

example :
    CoordinateMetric .timeNegative 1 ⊤ :=
  nullMetric

example (x : MinkowskiModel 1) :
    nullMetric.form x = nullForm :=
  nullMetric_form x

end ProjectAinos.SmoothGeometry.CoordinateMetric

end CoordinateFrameCriterion

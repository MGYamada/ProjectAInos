/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.NewtonHarmonics
import ProjectAinos.SpecialFunctions.SphericalComplex

open MvPolynomial ProjectAinos.SpecialFunctions
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
open ProjectAinos.SpecialFunctions.SphericalHarmonics

noncomputable section

example (d : ℕ) : UnitSphere d = Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := rfl

example (d k : ℕ) (p : homogeneousSubmodule (Fin d) ℝ k) (u : UnitSphere d) :
    restrict d k p u = eval u.val p.val := rfl

example {d : ℕ} (hd : 0 < d) (k : ℕ) : Function.Injective (restrict d k) := restrict_injective hd k

example (d k : ℕ) : space d k = (harmonics d k).map (restrict d k) := rfl

example {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (space d k) = Module.finrank ℝ (harmonics d k) := finrank_space hd k

example (k : ℕ) : Module.finrank ℝ (space 3 k) = 2 * k + 1 := finrank_space_three k

example {d k : ℕ} (p : harmonics d k) (u : UnitSphere d) :
    eval u.val (angularLaplacian d p.val.val) =
      -((k : ℝ) * (k + d - 2 : ℝ)) * restrict d k p.val u := angular_eigenvalue p u

example {k : ℕ} (p : harmonics 4 k) (u : UnitSphere 4) :
    eval u.val (angularLaplacian 4 p.val.val) = -((k : ℝ) * (k + 2)) * restrict 4 k p.val u :=
  angular_eigenvalue_three_sphere p u

example (n m : ℕ) {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1) :
    (∫ u : UnitSphere 3, (Legendre.polynomial n).eval (inner ℝ u.val e) *
      (Legendre.polynomial m).eval (inner ℝ u.val e)
      ∂ProjectAinos.SmoothGeometry.Sphere.sphereMeasure) =
      if n = m then 4 * Real.pi / (2 * (n : ℝ) + 1) else 0 := integral_zonal_mul n m he

open MeasureTheory ProjectAinos.SmoothGeometry.Sphere

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (F : E → ℝ) (f : Metric.sphere (0 : E) 1 → ℝ) (h : ℝ → ℝ)
    (hh : ∀ (u : Metric.sphere (0 : E) 1) (r : ℝ), 0 < r → F (r • u.val) = f u * h r) :
    ∫ x, F x ∂μ = (∫ u, f u ∂μ.toSphere) *
      ∫ r in Set.Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) * h r :=
  integral_polar_mul μ F f h hh

example {d k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k)
    (a : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    eval (a • u) p = a ^ k * eval u p := eval_smul hp a u

example {d k m : ℕ} (hd : 0 < d) (hne : k ≠ m) {f g : UnitSphere d → ℝ}
    (hf : f ∈ space d k) (hg : g ∈ space d m) :
    ∫ u, f u * g u ∂surfaceMeasure d = 0 := integral_mul_eq_zero hd hne hf hg

example (d : ℕ) (p : MvPolynomial (Fin d) ℝ) (u : UnitSphere d) :
    onSphere d p u = eval u.val p := rfl

example (d : ℕ) : surfaceMeasure d = (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := rfl

example (d k : ℕ) : continuousSpace d k =
    (harmonics d k).map
      ((onSphere d).toLinearMap.comp (homogeneousSubmodule (Fin d) ℝ k).subtype) := rfl

example {d : ℕ} (hd : 0 < d) : Dense (↑(⨆ k, continuousSpace d k) : Set C(UnitSphere d, ℝ)) :=
  continuousSpace_dense hd

example (d k : ℕ) : l2Space d k =
    (continuousSpace d k).map (ContinuousMap.toLp 2 (surfaceMeasure d) ℝ).toLinearMap := rfl

example {d : ℕ} (hd : 0 < d) : (⨆ k, l2Space d k).topologicalClosure = ⊤ := l2Space_dense hd

example {d : ℕ} (hd : 0 < d) :
    IsHilbertSum ℝ (fun k => l2Space d k) (fun k => (l2Space d k).subtypeₗᵢ) := isHilbertSum hd

example (d k : ℕ) : FiniteDimensional ℝ (l2Space d k) := inferInstance

example (d k : ℕ) : l2Space d k →ₗ[ℝ] C(UnitSphere d, ℝ) := representative d k

example {d k : ℕ} (f : l2Space d k) :
    ContinuousMap.toLp 2 (surfaceMeasure d) ℝ (representative d k f) = f.val :=
  toLp_representative f

example {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (l2Space d k) = Module.finrank ℝ (harmonics d k) := finrank_l2Space hd k

example (v : UnitSphere 3) (n : ℕ) : ∃ p : harmonics 3 n, ∀ u : UnitSphere 3,
    restrict 3 n p.val u = (Legendre.polynomial n).eval (inner ℝ u.val v.val) := exists_solidZonal v n

example {n : ℕ} (b : OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n)) (u v : UnitSphere 3) :
    ∑ i, representative 3 n (b i) u * representative 3 n (b i) v =
      (2 * (n : ℝ) + 1) / (4 * Real.pi) * (Legendre.polynomial n).eval (inner ℝ u.val v.val) :=
  addition b u v

example {d : ℕ} (hd : 0 < d) (k : ℕ) : harmonics d k ≃ₗ[ℝ] l2Space d k := harmonicsEquivL2 hd k

example {d : ℕ} (hd : 0 < d) (k : ℕ) (p : harmonics d k) :
    representative d k (harmonicsEquivL2 hd k p) = onSphere d p.val.val :=
  representative_harmonicsEquivL2 hd k p

example (n b : ℕ) (p : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ := extension n b p

example (n b : ℕ) {p : MvPolynomial (Fin 2) ℝ} (hp : p.IsHomogeneous n) :
    (extension n b p).IsHomogeneous (b + n) := homogeneous_extension n b hp

example (n b : ℕ) (hb : b ≤ 1) {p : MvPolynomial (Fin 2) ℝ} (hp : p.IsHomogeneous n) :
    laplacian 3 (extension n b p) = 0 := harmonic_extension n hb hp

example (j : ℕ) : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ := normalCoeff j

example (n b j : ℕ) (p : MvPolynomial (Fin 2) ℝ) (hj : j < b + 2) :
    normalCoeff j (extension n b p) = if b = j then p else 0 := normalCoeff_extension n b j p hj

example (n : ℕ) (i : Fin (2 * n + 1)) : ℕ × (Fin 2 →₀ ℕ) := cauchyExponents n i

example (n : ℕ) (i : Fin (2 * n + 1)) : (cauchyExponents n i).1 ≤ min 1 n ∧
    (cauchyExponents n i).2.degree = n - (cauchyExponents n i).1 := cauchyExponents_spec n i

example (n : ℕ) (i : Fin (2 * n + 1)) : harmonics 3 n := solidBasisVector n i

example (n : ℕ) : LinearIndependent ℝ (solidBasisVector n) := linearIndependent_solidBasisVector n

example (n : ℕ) : Module.Basis (Fin (2 * n + 1)) ℝ (harmonics 3 n) := solidBasis n

example (n : ℕ) (i : Fin (2 * n + 1)) : solidBasis n i = solidBasisVector n i :=
  solidBasis_apply n i

example (n : ℕ) : OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n) := realBasis n

example (n : ℕ) (i : Fin (2 * n + 1)) : realBasis n i = InnerProductSpace.gramSchmidtNormed ℝ
    (fun j => harmonicsEquivL2 (by decide : 0 < 3) n (solidBasisVector n j)) i :=
  realBasis_apply n i

open ProjectAinos.SmoothGeometry.Potential

example (n : ℕ) (u v : UnitSphere 3) :
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel u.val (fun _ => -v.val) =
      (4 * Real.pi)⁻¹ * (Legendre.polynomial n).eval (inner ℝ u.val v.val) :=
  newtonKernel_unit_derivative n u v

example (n : ℕ) (f : l2Space 3 n) : harmonics 3 n := solidRepresentative n f

example {n : ℕ} (b : OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n)) (u : UnitSphere 3)
    {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin 3)) :
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel (r • u.val) (fun _ => -y) =
      ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
        ∑ i, representative 3 n (b i) u * eval y (solidRepresentative n (b i)).val.val :=
  newtonKernel_derivative_addition b u hr y

example (n : ℕ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) (y : EuclideanSpace ℝ (Fin 3)) :
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel x (fun _ => -y) =
      newtonKernel x * ((Legendre.polynomial n).eval (inner ℝ x y / (‖x‖ * ‖y‖)) *
        (‖y‖ / ‖x‖) ^ n) := newtonKernel_derivative_legendre n hx y

open scoped ComplexConjugate

example {n : ℕ} (c : EuclideanSpace ℂ (Fin (2 * n + 1))) (u : UnitSphere 3) :
    complexMode c u = ∑ i, c i * (representative 3 n (realBasis n i) u : ℂ) := rfl

example {n : ℕ} (c d : EuclideanSpace ℂ (Fin (2 * n + 1))) :
    ∫ u, conj (complexMode c u) * complexMode d u ∂sphereMeasure = inner ℂ c d :=
  integral_complexMode c d

example {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n + 1)) ℂ (EuclideanSpace ℂ (Fin (2 * n + 1))))
    (u v : UnitSphere 3) :
    ∑ i, complexMode (b i) u * conj (complexMode (b i) v) =
      (((2 * (n : ℝ) + 1) / (4 * Real.pi) *
        (Legendre.polynomial n).eval (inner ℝ u.val v.val) : ℝ) : ℂ) := addition_complex b u v

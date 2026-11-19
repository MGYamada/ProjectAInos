/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation

/-!
# Static coordinate metrics

A static metric is `ds² = −N(x)² dt² + γ_{αβ}(x) dx^α dx^β`, with a lapse `N` and a spatial
metric `γ` that depend only on the spatial point `x` of the event `z = (t, x)`
(`spatialPoint`, `staticCoefficient`). Staticity is built into the data: `N` and `γ` are
functions on the space `Fin (n + 1) → ℝ`, so every derivative along `e₀` vanishes
(`fderiv_comp_spatialPoint_zero`). Regular data on an open set `V` of space have a smooth
lapse without zeros and a smooth symmetric spatial metric with nonzero determinant
(`IsStaticRegularOn`).

* `staticCoefficient_inv`: the inverse is `g^{00} = −N⁻²`, `g^{0α} = 0`, `g^{αβ} = γ^{αβ}`.
* `christoffelOf_staticCoefficient_zero_zero_succ`, `…_zero_succ_zero`, `…_succ_zero_zero`,
  `…_succ_succ_succ`: `Γ⁰_{0α} = Γ⁰_{α0} = ∂_α N / N`, `Γ^α_{00} = N γ^{αβ} ∂_β N` and
  `Γ^μ_{αβ} = Γ̃^μ_{αβ}`, the Christoffel symbols of `γ` (`christoffelOf` of the spatial
  array); the others vanish (`…_zero_zero_zero`, `…_zero_succ_succ`, `…_succ_zero_succ`,
  `…_succ_succ_zero`).
* `fderiv_spatialInverse`, `fderiv_spatialInverse_eq_christoffel`: the derivative of the
  inverse spatial metric, `∂_a γ^{bc} = −γ^{bμ} ∂_a γ_{μν} γ^{νc}
  = −Γ̃^b_{aμ} γ^{μc} − Γ̃^c_{aμ} γ^{bμ}`.
* `divergence_eq_spatialLaplacian`: the Laplacian `Δ_γ f = γ^{αβ} (∂_α ∂_β f − Γ̃^μ_{αβ} ∂_μ f)`
  (`spatialLaplacian`) in divergence form, `∂_α (γ^{αβ} ∂_β f) + Γ̃^α_{αμ} γ^{μβ} ∂_β f`.
* `ricciOf_staticCoefficient_zero_zero`: **the time component of the Ricci tensor**,
  `R₀₀ = N Δ_γ N`.
* `staticMetric`, `coefficient_staticMetric`: the coordinate metric of regular static data
  with a positive definite `γ`, on the cylinder `ℝ × V` over an open set `V` of space
  (`staticDomain`); the instances `minkowskiStatic` (`N = 1`, `γ = 1`) and `expLapseStatic`
  (`N = e^{x¹}`, `γ = 1`, regular by `isStaticRegularOn_expLapse`), with `R₀₀ = e^{2x¹}`
  (`ricciOf_expLapseStatic_zero_zero`).
* `IsEinstein.ricciOf_eq`: the trace-reversed Einstein equations in four dimensions,
  `G_{ik} = κ T_{ik}` gives `R_{ik} = κ (T_{ik} − ½ g_{ik} g^{ac} T_{ac})`; with the static
  inverse, `g^{ac} T_{ac} = −T₀₀/N² + γ^{αβ} T_{αβ}` (`staticCoefficient_inv_trace`).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {n : ℕ}

/-! ### The spatial point of an event -/

variable (n) in
/-- The spatial projection `z ↦ (z¹, …, z^{n+1})`, a continuous linear map. -/
def spatialProjection : MinkowskiModel (n + 1) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun α => ContinuousLinearMap.proj α.succ

/-- The spatial point `x = (z¹, …, z^{n+1})` of an event `z = (z⁰, x)`. -/
def spatialPoint (z : MinkowskiModel (n + 1)) : Fin (n + 1) → ℝ := spatialProjection n z

/-- The spatial point is the spatial projection. -/
theorem spatialPoint_eq_spatialProjection :
    (spatialPoint : MinkowskiModel (n + 1) → Fin (n + 1) → ℝ) = spatialProjection n := rfl

/-- The components of the spatial point are the spatial components of the event. -/
@[simp] theorem spatialPoint_apply (z : MinkowskiModel (n + 1)) (α : Fin (n + 1)) :
    spatialPoint z α = z α.succ := rfl

/-- The time axis has no spatial part. -/
@[simp] theorem spatialPoint_single_zero :
    spatialPoint (Pi.single 0 1 : MinkowskiModel (n + 1)) = 0 := by
  funext α
  simp [Fin.succ_ne_zero]

/-- The spatial part of a spatial basis vector. -/
@[simp] theorem spatialPoint_single_succ (α : Fin (n + 1)) :
    spatialPoint (Pi.single α.succ 1 : MinkowskiModel (n + 1)) = Pi.single α 1 := by
  funext β
  simp [Pi.single_apply, Fin.succ_inj]

/-- The spatial point of the event `(t, x)` is `x`. -/
@[simp] theorem spatialPoint_cons (t : ℝ) (x : Fin (n + 1) → ℝ) :
    spatialPoint (Fin.cons t x : MinkowskiModel (n + 1)) = x := by
  funext α
  simp

/-- The derivative of a function of the spatial point. -/
theorem fderiv_comp_spatialPoint {f : (Fin (n + 1) → ℝ) → ℝ} {z : MinkowskiModel (n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPoint z)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => f (spatialPoint w)) z v =
      fderiv ℝ f (spatialPoint z) (spatialPoint v) := by
  have h := hf.hasFDerivAt.comp z (spatialProjection n).hasFDerivAt
  rw [show (fun w => f (spatialPoint w)) = f ∘ spatialPoint from rfl, h.fderiv]
  rfl

/-- A function of the spatial point does not change along the time axis. -/
theorem fderiv_comp_spatialPoint_zero {f : (Fin (n + 1) → ℝ) → ℝ} {z : MinkowskiModel (n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPoint z)) :
    fderiv ℝ (fun w => f (spatialPoint w)) z (Pi.single 0 1) = 0 := by
  rw [fderiv_comp_spatialPoint hf, spatialPoint_single_zero, map_zero]

/-- The derivative along a spatial axis is the spatial partial derivative. -/
theorem fderiv_comp_spatialPoint_succ {f : (Fin (n + 1) → ℝ) → ℝ} {z : MinkowskiModel (n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPoint z)) (α : Fin (n + 1)) :
    fderiv ℝ (fun w => f (spatialPoint w)) z (Pi.single α.succ 1) =
      fderiv ℝ f (spatialPoint z) (Pi.single α 1) := by
  rw [fderiv_comp_spatialPoint hf, spatialPoint_single_succ]

/-! ### Static coefficients -/

/-- The static coefficients `g₀₀ = −N(x)²`, `g₀α = g_α0 = 0`, `g_{αβ} = γ_{αβ}(x)` at the event
`z` with spatial point `x`. -/
def staticCoefficient (N : (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : MinkowskiModel (n + 1)) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons (-N (spatialPoint z) ^ 2) fun _ => 0)
    fun α => Fin.cons 0 fun β => γ (spatialPoint z) α β)

variable {N : (Fin (n + 1) → ℝ) → ℝ}
  {γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- `g₀₀ = −N²`. -/
@[simp] theorem staticCoefficient_zero_zero (z : MinkowskiModel (n + 1)) :
    staticCoefficient N γ z 0 0 = -N (spatialPoint z) ^ 2 := rfl

/-- `g₀β = 0`. -/
@[simp] theorem staticCoefficient_zero_succ (z : MinkowskiModel (n + 1)) (β : Fin (n + 1)) :
    staticCoefficient N γ z 0 β.succ = 0 := rfl

/-- `g_α0 = 0`. -/
@[simp] theorem staticCoefficient_succ_zero (z : MinkowskiModel (n + 1)) (α : Fin (n + 1)) :
    staticCoefficient N γ z α.succ 0 = 0 := rfl

/-- `g_{αβ} = γ_{αβ}`. -/
@[simp] theorem staticCoefficient_succ_succ (z : MinkowskiModel (n + 1)) (α β : Fin (n + 1)) :
    staticCoefficient N γ z α.succ β.succ = γ (spatialPoint z) α β := rfl

/-- The inverse of the static coefficients: `g^{00} = −N⁻²`, `g^{0α} = 0`, `g^{αβ} = γ^{αβ}`. -/
def staticInverse (N : (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : MinkowskiModel (n + 1)) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons (-(N (spatialPoint z) ^ 2)⁻¹) fun _ => 0)
    fun α => Fin.cons 0 fun β => (γ (spatialPoint z))⁻¹ α β)

/-- `staticInverse` is the inverse matrix where `N ≠ 0` and `det γ ≠ 0`. -/
theorem staticCoefficient_inv {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
    (hγ : (γ (spatialPoint z)).det ≠ 0) :
    (staticCoefficient N γ z)⁻¹ = staticInverse N γ z := by
  refine Matrix.inv_eq_right_inv ?_
  have hγ' : γ (spatialPoint z) * (γ (spatialPoint z))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ)
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun α => ?_) i <;> refine Fin.cases ?_ (fun β => ?_) j
  · simp [staticInverse, staticCoefficient, hN]
  · simp [staticInverse, staticCoefficient, (Fin.succ_ne_zero β).symm]
  · simp [staticInverse, staticCoefficient, Fin.succ_ne_zero]
  · have h := congrFun (congrFun hγ' α) β
    rw [Matrix.mul_apply] at h
    simpa [staticInverse, staticCoefficient, Matrix.one_apply, Fin.succ_inj] using h

section Inverse

variable {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
  (hγ : (γ (spatialPoint z)).det ≠ 0)
include hN hγ

/-- `g^{00} = −N⁻²`. -/
theorem staticCoefficient_inv_zero_zero :
    (staticCoefficient N γ z)⁻¹ 0 0 = -(N (spatialPoint z) ^ 2)⁻¹ := by
  rw [staticCoefficient_inv hN hγ]
  rfl

/-- `g^{0β} = 0`. -/
theorem staticCoefficient_inv_zero_succ (β : Fin (n + 1)) :
    (staticCoefficient N γ z)⁻¹ 0 β.succ = 0 := by
  rw [staticCoefficient_inv hN hγ]
  rfl

/-- `g^{α0} = 0`. -/
theorem staticCoefficient_inv_succ_zero (α : Fin (n + 1)) :
    (staticCoefficient N γ z)⁻¹ α.succ 0 = 0 := by
  rw [staticCoefficient_inv hN hγ]
  rfl

/-- `g^{αβ} = γ^{αβ}`. -/
theorem staticCoefficient_inv_succ_succ (α β : Fin (n + 1)) :
    (staticCoefficient N γ z)⁻¹ α.succ β.succ = (γ (spatialPoint z))⁻¹ α β := by
  rw [staticCoefficient_inv hN hγ]
  rfl

end Inverse

/-! ### Derivatives of the coefficients -/

section Derivatives

variable {z : MinkowskiModel (n + 1)}

/-- `∂ g₀₀ = −2N ∂N`. -/
theorem fderiv_staticCoefficient_zero_zero (hN : DifferentiableAt ℝ N (spatialPoint z))
    (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w 0 0) z v =
      -(2 * N (spatialPoint z) * fderiv ℝ N (spatialPoint z) (spatialPoint v)) := by
  have hd : DifferentiableAt ℝ (fun y => -N y ^ 2) (spatialPoint z) := (hN.pow 2).neg
  change fderiv ℝ (fun w => (fun y => -N y ^ 2) (spatialPoint w)) z v = _
  rw [fderiv_comp_spatialPoint hd, fderiv_fun_neg, fderiv_fun_pow 2 hN]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `∂ g₀β = 0`. -/
theorem fderiv_staticCoefficient_zero_succ (β : Fin (n + 1)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w 0 β.succ) z v = 0 := by
  change fderiv ℝ (fun _ => (0 : ℝ)) z v = 0
  simp

/-- `∂ g_α0 = 0`. -/
theorem fderiv_staticCoefficient_succ_zero (α : Fin (n + 1)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w α.succ 0) z v = 0 := by
  change fderiv ℝ (fun _ => (0 : ℝ)) z v = 0
  simp

/-- `∂ g_{αβ} = ∂ γ_{αβ}`, with the spatial part of the direction. -/
theorem fderiv_staticCoefficient_succ_succ (α β : Fin (n + 1))
    (hγ : DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w α.succ β.succ) z v =
      fderiv ℝ (fun y => γ y α β) (spatialPoint z) (spatialPoint v) := by
  change fderiv ℝ (fun w => (fun y => γ y α β) (spatialPoint w)) z v = _
  rw [fderiv_comp_spatialPoint hγ]

end Derivatives

/-! ### The Christoffel symbols -/

section Christoffel

variable {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
  (hγ : (γ (spatialPoint z)).det ≠ 0)
include hN hγ

/-- `Γ⁰₀₀ = 0`. -/
theorem christoffelOf_staticCoefficient_zero_zero_zero
    (hNd : DifferentiableAt ℝ N (spatialPoint z)) :
    christoffelOf (staticCoefficient N γ) z 0 0 0 = 0 := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_zero_zero hNd, fderiv_staticCoefficient_succ_zero,
    fderiv_staticCoefficient_zero_succ, spatialPoint_single_zero, map_zero]
  simp [staticInverse]

/-- `Γ⁰_{0α} = ∂_α N / N`. -/
theorem christoffelOf_staticCoefficient_zero_zero_succ
    (hNd : DifferentiableAt ℝ N (spatialPoint z)) (α : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z 0 0 α.succ =
      fderiv ℝ N (spatialPoint z) (Pi.single α 1) / N (spatialPoint z) := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_zero_zero hNd, fderiv_staticCoefficient_succ_zero,
    fderiv_staticCoefficient_zero_succ, spatialPoint_single_succ]
  simp [staticInverse]
  field_simp

/-- `Γ⁰_{α0} = ∂_α N / N`. -/
theorem christoffelOf_staticCoefficient_zero_succ_zero
    (hNd : DifferentiableAt ℝ N (spatialPoint z)) (α : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z 0 α.succ 0 =
      fderiv ℝ N (spatialPoint z) (Pi.single α 1) / N (spatialPoint z) := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_zero_zero hNd, fderiv_staticCoefficient_succ_zero,
    fderiv_staticCoefficient_zero_succ, spatialPoint_single_succ]
  simp [staticInverse]
  field_simp

/-- `Γ⁰_{αβ} = 0`. -/
theorem christoffelOf_staticCoefficient_zero_succ_succ
    (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (α β : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z 0 α.succ β.succ = 0 := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_succ_zero, fderiv_staticCoefficient_zero_succ,
    fderiv_staticCoefficient_succ_succ _ _ (hγd _ _), spatialPoint_single_zero, map_zero]
  simp [staticInverse]

/-- `Γ^μ_{00} = N γ^{μν} ∂_ν N`. -/
theorem christoffelOf_staticCoefficient_succ_zero_zero
    (hNd : DifferentiableAt ℝ N (spatialPoint z)) (μ : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ 0 0 =
      N (spatialPoint z) * ∑ ν, (γ (spatialPoint z))⁻¹ μ ν *
        fderiv ℝ N (spatialPoint z) (Pi.single ν 1) := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_zero_zero hNd, fderiv_staticCoefficient_succ_zero,
    fderiv_staticCoefficient_zero_succ, spatialPoint_single_zero, spatialPoint_single_succ,
    map_zero]
  simp [staticInverse, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- `Γ^μ_{0β} = 0`. -/
theorem christoffelOf_staticCoefficient_succ_zero_succ
    (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (μ β : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ 0 β.succ = 0 := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_succ_zero, fderiv_staticCoefficient_zero_succ,
    fderiv_staticCoefficient_succ_succ _ _ (hγd _ _), spatialPoint_single_zero, map_zero]
  simp [staticInverse]

/-- `Γ^μ_{α0} = 0`. -/
theorem christoffelOf_staticCoefficient_succ_succ_zero
    (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (μ α : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ α.succ 0 = 0 := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_succ_zero, fderiv_staticCoefficient_zero_succ,
    fderiv_staticCoefficient_succ_succ _ _ (hγd _ _), spatialPoint_single_zero, map_zero]
  simp [staticInverse]

/-- `Γ^μ_{αβ} = Γ̃^μ_{αβ}`: the spatial symbols are the Christoffel symbols of `γ`. -/
theorem christoffelOf_staticCoefficient_succ_succ_succ
    (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (μ α β : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ α.succ β.succ =
      christoffelOf γ (spatialPoint z) μ α β := by
  unfold christoffelOf
  rw [Fin.sum_univ_succ, staticCoefficient_inv hN hγ]
  simp only [fderiv_staticCoefficient_succ_zero, fderiv_staticCoefficient_zero_succ,
    fderiv_staticCoefficient_succ_succ _ _ (hγd _ _), spatialPoint_single_succ]
  simp [staticInverse]

end Christoffel

/-! ### The derivative of the inverse spatial metric -/

section SpatialInverse

variable {V : Set (Fin (n + 1) → ℝ)}

/-- The entries of the inverse spatial metric are smooth where the determinant does not
vanish. -/
theorem contDiffAt_spatialInverse (hV : IsOpen V)
    (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) {x : Fin (n + 1) → ℝ} (hx : x ∈ V)
    (hdet : (γ x).det ≠ 0) (a b : Fin (n + 1)) :
    ContDiffAt ℝ ∞ (fun y => (γ y)⁻¹ a b) x := by
  have hC : ContDiffAt ℝ ∞ (fun y => fun i j => γ y i j) x :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j =>
      (hγs i j).contDiffAt (hV.mem_nhds hx)
  exact (contDiffAt_matrix_inv_apply hdet a b).comp x hC

/-- **The derivative of the inverse matrix**: `∂ γ^{ab} = −γ^{aμ} (∂ γ_{μν}) γ^{νb}`. -/
theorem fderiv_spatialInverse (hV : IsOpen V)
    (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hdet : ∀ x ∈ V, (γ x).det ≠ 0)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ V) (a b : Fin (n + 1)) (v : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun y => (γ y)⁻¹ a b) x v =
      -∑ μ, ∑ ν, (γ x)⁻¹ a μ * fderiv ℝ (fun y => γ y μ ν) x v * (γ x)⁻¹ ν b := by
  have hU := hV.mem_nhds hx
  have hdγ (i j : Fin (n + 1)) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    ((hγs i j).contDiffAt hU).differentiableAt (by simp)
  have hdi (i j : Fin (n + 1)) : DifferentiableAt ℝ (fun y => (γ y)⁻¹ i j) x :=
    (contDiffAt_spatialInverse hV hγs hx (hdet x hx) i j).differentiableAt (by simp)
  set g := (γ x)⁻¹ with hg
  let Dγ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => fderiv ℝ (fun y => γ y i j) x v
  let Di : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => fderiv ℝ (fun y => (γ y)⁻¹ i j) x v
  have hprod : γ x * Di + Dγ * g = 0 := by
    ext μ c
    have hev : (fun y => ∑ ν, γ y μ ν * (γ y)⁻¹ ν c) =ᶠ[𝓝 x]
        fun _ => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) μ c := by
      filter_upwards [hU] with y hy
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet y hy))]
    have h := congrArg (fun L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ => L v) hev.fderiv_eq
    simp only [fderiv_const_apply, zero_apply] at h
    rw [fderiv_fun_sum fun ν _ => (hdγ μ ν).fun_mul (hdi ν c)] at h
    simp only [sum_apply] at h
    rw [Finset.sum_congr rfl fun ν _ => by rw [fderiv_fun_mul (hdγ μ ν) (hdi ν c)]] at h
    simp only [add_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Dγ, Di, Matrix.of_apply]
    rw [← h, hg]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  have hinv : g * γ x = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x hx))
  have hDi : Di = -(g * Dγ * g) := by
    calc Di = g * (γ x * Di) := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = g * (-(Dγ * g)) := by rw [eq_neg_of_add_eq_zero_left hprod]
      _ = -(g * Dγ * g) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have h := congrFun (congrFun hDi a) b
  simp only [Di, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, Dγ] at h
  rw [h, Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- **The inverse spatial metric is parallel**:
`∂_a γ^{bc} = −Γ̃^b_{aμ} γ^{μc} − Γ̃^c_{aμ} γ^{bμ}` for a symmetric spatial metric. -/
theorem fderiv_spatialInverse_eq_christoffel (hV : IsOpen V)
    (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hdet : ∀ x ∈ V, (γ x).det ≠ 0)
    (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α) {x : Fin (n + 1) → ℝ} (hx : x ∈ V)
    (a b c : Fin (n + 1)) :
    fderiv ℝ (fun y => (γ y)⁻¹ b c) x (Pi.single a 1) =
      -∑ μ, (christoffelOf γ x b a μ * (γ x)⁻¹ μ c +
        christoffelOf γ x c a μ * (γ x)⁻¹ b μ) := by
  rw [fderiv_spatialInverse hV hγs hdet hx]
  have hDs (i j k : Fin (n + 1)) :
      fderiv ℝ (fun y => γ y j k) x (Pi.single i 1) =
        fderiv ℝ (fun y => γ y k j) x (Pi.single i 1) := by
    have hev : (fun y => γ y j k) =ᶠ[𝓝 x] fun y => γ y k j :=
      eventually_of_mem (hV.mem_nhds hx) fun y hy => hsymm y hy j k
    rw [hev.fderiv_eq]
  have hgs (i j : Fin (n + 1)) : (γ x)⁻¹ i j = (γ x)⁻¹ j i := by
    have hT : Matrix.transpose (γ x) = γ x := Matrix.ext fun i j => hsymm x hx j i
    have h := congrFun (congrFun (Matrix.transpose_nonsing_inv (γ x)) j) i
    rw [hT, Matrix.transpose_apply] at h
    exact h
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun l μ =>
    (fderiv ℝ (fun y => γ y μ l) x (Pi.single a 1) +
      fderiv ℝ (fun y => γ y l a) x (Pi.single μ 1) -
      fderiv ℝ (fun y => γ y a μ) x (Pi.single l 1)) / 2
  have hΓ (k μ : Fin (n + 1)) : christoffelOf γ x k a μ = ∑ l, (γ x)⁻¹ k l * L l μ := by
    simp only [christoffelOf, L, Matrix.of_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hLL (l μ : Fin (n + 1)) :
      L l μ + L μ l = fderiv ℝ (fun y => γ y l μ) x (Pi.single a 1) := by
    simp only [L, Matrix.of_apply]
    rw [hDs a μ l, hDs μ l a, hDs l a μ]
    ring
  have h1 : ∑ μ, christoffelOf γ x b a μ * (γ x)⁻¹ μ c =
      ∑ μ, ∑ l, (γ x)⁻¹ b l * L l μ * (γ x)⁻¹ μ c := by
    simp only [hΓ, Finset.sum_mul]
  have h2 : ∑ μ, christoffelOf γ x c a μ * (γ x)⁻¹ b μ =
      ∑ μ, ∑ l, (γ x)⁻¹ b l * L μ l * (γ x)⁻¹ μ c := by
    simp only [hΓ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hgs c μ]
    ring
  rw [Finset.sum_add_distrib, h1, h2, ← Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hLL l μ]
  ring

end SpatialInverse

/-! ### The Laplacian of a spatial metric -/

/-- The Laplacian `Δ_γ f = γ^{αβ} (∂_α ∂_β f − Γ̃^μ_{αβ} ∂_μ f)` of a spatial metric `γ`, with
the Christoffel symbols `Γ̃` of `γ`. -/
def spatialLaplacian (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (f : (Fin (n + 1) → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ α, ∑ β, (γ x)⁻¹ α β *
    (fderiv ℝ (fun y => fderiv ℝ f y (Pi.single β 1)) x (Pi.single α 1) -
      ∑ μ, christoffelOf γ x μ α β * fderiv ℝ f x (Pi.single μ 1))

section Laplacian

variable {V : Set (Fin (n + 1) → ℝ)}

/-- **The Laplacian in divergence form**:
`∂_α (γ^{αβ} ∂_β f) + Γ̃^α_{αμ} γ^{μβ} ∂_β f = Δ_γ f`. -/
theorem divergence_eq_spatialLaplacian (hV : IsOpen V)
    (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hdet : ∀ x ∈ V, (γ x).det ≠ 0)
    (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f V) {x : Fin (n + 1) → ℝ} (hx : x ∈ V) :
    ∑ α, fderiv ℝ (fun y => ∑ β, (γ y)⁻¹ α β * fderiv ℝ f y (Pi.single β 1)) x
        (Pi.single α 1) +
      ∑ α, ∑ μ, christoffelOf γ x α α μ *
        ∑ β, (γ x)⁻¹ μ β * fderiv ℝ f x (Pi.single β 1) =
      spatialLaplacian γ f x := by
  have hU := hV.mem_nhds hx
  have hdi (i j : Fin (n + 1)) : DifferentiableAt ℝ (fun y => (γ y)⁻¹ i j) x :=
    (contDiffAt_spatialInverse hV hγs hx (hdet x hx) i j).differentiableAt (by simp)
  have hdf (β : Fin (n + 1)) :
      DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single β 1)) x := by
    have h : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single β 1)) V :=
      (hf.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
    exact (h.contDiffAt hU).differentiableAt (by simp)
  have hterm (α : Fin (n + 1)) :
      fderiv ℝ (fun y => ∑ β, (γ y)⁻¹ α β * fderiv ℝ f y (Pi.single β 1)) x (Pi.single α 1) =
        ∑ β, ((γ x)⁻¹ α β *
            fderiv ℝ (fun y => fderiv ℝ f y (Pi.single β 1)) x (Pi.single α 1) +
          fderiv ℝ f x (Pi.single β 1) *
            fderiv ℝ (fun y => (γ y)⁻¹ α β) x (Pi.single α 1)) := by
    rw [fderiv_fun_sum fun β _ => (hdi α β).fun_mul (hdf β), sum_apply]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [fderiv_fun_mul (hdi α β) (hdf β)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [hterm, fderiv_spatialInverse_eq_christoffel hV hγs hdet hsymm hx]
  unfold spatialLaplacian
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e1 : ∑ β, fderiv ℝ f x (Pi.single β 1) *
      ∑ μ, christoffelOf γ x α α μ * (γ x)⁻¹ μ β =
      ∑ μ, christoffelOf γ x α α μ * ∑ β, (γ x)⁻¹ μ β * fderiv ℝ f x (Pi.single β 1) := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => by ring
  have e2 : ∑ β, fderiv ℝ f x (Pi.single β 1) *
      ∑ μ, christoffelOf γ x β α μ * (γ x)⁻¹ α μ =
      ∑ β, (γ x)⁻¹ α β * ∑ μ, christoffelOf γ x μ α β * fderiv ℝ f x (Pi.single μ 1) := by
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => by ring
  simp only [Finset.sum_add_distrib, mul_neg, mul_add, mul_sub, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib]
  linear_combination -e1 - e2

end Laplacian

/-! ### The time component of the Ricci tensor -/

/-- Regular static data on a set `V` of space: `V` is open, the lapse `N` and the entries of the
spatial metric `γ` are smooth on `V`, `N` has no zero, and `γ` is symmetric with nonzero
determinant. -/
structure IsStaticRegularOn (N : (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (V : Set (Fin (n + 1) → ℝ)) : Prop where
  /-- The set of space is open. -/
  isOpen : IsOpen V
  /-- The lapse is smooth. -/
  lapse_smooth : ContDiffOn ℝ ∞ N V
  /-- The spatial metric is smooth. -/
  spatial_smooth : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V
  /-- The lapse has no zero. -/
  lapse_ne_zero : ∀ x ∈ V, N x ≠ 0
  /-- The spatial metric is invertible. -/
  det_ne_zero : ∀ x ∈ V, (γ x).det ≠ 0
  /-- The spatial metric is symmetric. -/
  symm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α

namespace IsStaticRegularOn

variable {V : Set (Fin (n + 1) → ℝ)} (h : IsStaticRegularOn N γ V)
include h

/-- The lapse is differentiable on `V`. -/
theorem lapse_differentiableAt {x : Fin (n + 1) → ℝ} (hx : x ∈ V) :
    DifferentiableAt ℝ N x :=
  (h.lapse_smooth.contDiffAt (h.isOpen.mem_nhds hx)).differentiableAt (by simp)

/-- The entries of the spatial metric are differentiable on `V`. -/
theorem spatial_differentiableAt {x : Fin (n + 1) → ℝ} (hx : x ∈ V) (α β : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => γ y α β) x :=
  ((h.spatial_smooth α β).contDiffAt (h.isOpen.mem_nhds hx)).differentiableAt (by simp)

end IsStaticRegularOn

/-- **The time component of the Ricci tensor of a static metric**: `R₀₀ = N Δ_γ N`, with the
Laplacian `Δ_γ N = γ^{αβ} (∂_α ∂_β N − Γ̃^μ_{αβ} ∂_μ N)` of the spatial metric. -/
theorem ricciOf_staticCoefficient_zero_zero {V : Set (Fin (n + 1) → ℝ)}
    (h : IsStaticRegularOn N γ V) {z : MinkowskiModel (n + 1)} (hz : spatialPoint z ∈ V) :
    ricciOf (staticCoefficient N γ) z 0 0 =
      N (spatialPoint z) * spatialLaplacian γ N (spatialPoint z) := by
  have hS : spatialPoint ⁻¹' V ∈ 𝓝 z :=
    (h.isOpen.preimage (spatialProjection n).continuous).mem_nhds hz
  have hU := h.isOpen.mem_nhds hz
  have hN0 := h.lapse_ne_zero _ hz
  have hdet := h.det_ne_zero _ hz
  have hNd := h.lapse_differentiableAt hz
  have hγd := h.spatial_differentiableAt hz
  have hdi (i j : Fin (n + 1)) : DifferentiableAt ℝ (fun y => (γ y)⁻¹ i j) (spatialPoint z) :=
    (contDiffAt_spatialInverse h.isOpen h.spatial_smooth hz hdet i j).differentiableAt
      (by simp)
  have hdf (β : Fin (n + 1)) :
      DifferentiableAt ℝ (fun y => fderiv ℝ N y (Pi.single β 1)) (spatialPoint z) := by
    have h' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ N y (Pi.single β 1)) V :=
      (h.lapse_smooth.fderiv_of_isOpen h.isOpen (by simp)).clm_apply contDiffOn_const
    exact (h'.contDiffAt hU).differentiableAt (by simp)
  obtain ⟨W, hW⟩ : ∃ W : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ,
      W = fun α y => ∑ β, (γ y)⁻¹ α β * fderiv ℝ N y (Pi.single β 1) := ⟨_, rfl⟩
  have hWd (α : Fin (n + 1)) : DifferentiableAt ℝ (W α) (spatialPoint z) := by
    rw [hW]
    exact DifferentiableAt.fun_sum fun β _ => (hdi α β).fun_mul (hdf β)
  have hA (w : MinkowskiModel (n + 1)) (hw : spatialPoint w ∈ V) (μ : Fin (n + 1)) :
      christoffelOf (staticCoefficient N γ) w μ.succ 0 0 =
        N (spatialPoint w) * W μ (spatialPoint w) := by
    rw [christoffelOf_staticCoefficient_succ_zero_zero (h.lapse_ne_zero _ hw)
      (h.det_ne_zero _ hw) (h.lapse_differentiableAt hw), hW]
  have hE1 (α : Fin (n + 1)) :
      (fun w => christoffelOf (staticCoefficient N γ) w α.succ 0 0) =ᶠ[𝓝 z]
        fun w => (fun y => N y * W α y) (spatialPoint w) := by
    filter_upwards [hS] with w hw
    exact hA w hw α
  have hE2 (α : Fin (n + 1)) :
      (fun w => christoffelOf (staticCoefficient N γ) w α.succ α.succ 0) =ᶠ[𝓝 z]
        fun _ => 0 := by
    filter_upwards [hS] with w hw
    exact christoffelOf_staticCoefficient_succ_succ_zero (h.lapse_ne_zero _ hw)
      (h.det_ne_zero _ hw) (h.spatial_differentiableAt hw) α α
  have hterm (α : Fin (n + 1)) :
      fderiv ℝ (fun w => christoffelOf (staticCoefficient N γ) w α.succ 0 0) z
          (Pi.single α.succ 1) -
        fderiv ℝ (fun w => christoffelOf (staticCoefficient N γ) w α.succ α.succ 0) z
          (Pi.single 0 1) +
        ∑ a, (christoffelOf (staticCoefficient N γ) z α.succ α.succ a *
            christoffelOf (staticCoefficient N γ) z a 0 0 -
          christoffelOf (staticCoefficient N γ) z α.succ 0 a *
            christoffelOf (staticCoefficient N γ) z a α.succ 0) =
      N (spatialPoint z) * (fderiv ℝ (W α) (spatialPoint z) (Pi.single α 1) +
        ∑ μ, christoffelOf γ (spatialPoint z) α α μ * W μ (spatialPoint z)) := by
    rw [(hE1 α).fderiv_eq, (hE2 α).fderiv_eq, fderiv_comp_spatialPoint_succ (hNd.fun_mul (hWd α)),
      fderiv_fun_mul hNd (hWd α), Fin.sum_univ_succ]
    simp only [fderiv_const_apply, zero_apply, add_apply, smul_apply, smul_eq_mul,
      hA z hz, christoffelOf_staticCoefficient_succ_succ_zero hN0 hdet hγd,
      christoffelOf_staticCoefficient_zero_zero_zero hN0 hdet hNd,
      christoffelOf_staticCoefficient_zero_succ_zero hN0 hdet hNd,
      christoffelOf_staticCoefficient_succ_zero_succ hN0 hdet hγd,
      christoffelOf_staticCoefficient_succ_succ_succ hN0 hdet hγd, mul_zero, sub_zero, zero_sub]
    rw [mul_add, Finset.mul_sum]
    field_simp
    ring_nf
  unfold ricciOf
  rw [Fin.sum_univ_succ]
  simp only [sub_self, zero_add, Finset.sum_const_zero, hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← divergence_eq_spatialLaplacian h.isOpen
    h.spatial_smooth h.det_ne_zero h.symm h.lapse_smooth hz, hW]

/-! ### The static coordinate metric -/

/-- The cylinder `ℝ × V` of the events whose spatial point lies in the open set `V`. -/
def staticDomain (V : Opens (Fin (n + 1) → ℝ)) : Opens (MinkowskiModel (n + 1)) :=
  ⟨spatialPoint ⁻¹' V, V.isOpen.preimage (spatialProjection n).continuous⟩

/-- An event lies in the cylinder over `V` when its spatial point lies in `V`. -/
@[simp] theorem mem_staticDomain {V : Opens (Fin (n + 1) → ℝ)} {z : MinkowskiModel (n + 1)} :
    z ∈ staticDomain V ↔ spatialPoint z ∈ V := Iff.rfl

/-- The static coefficients are symmetric where the spatial metric is. -/
theorem staticCoefficient_symm {z : MinkowskiModel (n + 1)}
    (hsymm : ∀ α β, γ (spatialPoint z) α β = γ (spatialPoint z) β α) (i k : Fin (n + 1 + 1)) :
    staticCoefficient N γ z i k = staticCoefficient N γ z k i := by
  refine Fin.cases ?_ (fun α => ?_) i <;> refine Fin.cases ?_ (fun β => ?_) k
  · rfl
  · rfl
  · rfl
  · exact hsymm α β

/-- The entries of the static coefficients are smooth on the cylinder over `V`. -/
theorem contDiffOn_staticCoefficient {V : Opens (Fin (n + 1) → ℝ)} (hN : ContDiffOn ℝ ∞ N V)
    (hγ : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (i k : Fin (n + 1 + 1)) :
    ContDiffOn ℝ ∞ (fun z => staticCoefficient N γ z i k) (staticDomain V) := by
  have hP : MapsTo spatialPoint (staticDomain V : Set (MinkowskiModel (n + 1))) V :=
    fun _ hz => hz
  refine Fin.cases ?_ (fun α => ?_) i <;> refine Fin.cases ?_ (fun β => ?_) k
  · exact ((hN.comp (spatialProjection n).contDiff.contDiffOn hP).pow 2).neg
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact (hγ α β).comp (spatialProjection n).contDiff.contDiffOn hP

/-- **The static coordinate metric** `−N² dt² + γ_{αβ} dx^α dx^β` on the cylinder over `V`, for
a smooth lapse without zeros and a smooth, symmetric, positive definite spatial metric on
`V`. -/
def staticMetric (N : (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (V : Opens (Fin (n + 1) → ℝ)) (hN : ContDiffOn ℝ ∞ N V)
    (hγ : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hN0 : ∀ x ∈ V, N x ≠ 0)
    (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α)
    (hpos : ∀ x ∈ V, ∀ v : Fin (n + 1) → ℝ, v ≠ 0 → 0 < ∑ α, ∑ β, γ x α β * v α * v β) :
    CoordinateMetric .timeNegative (n + 1) (staticDomain V) :=
  ofCriterion (coefficientForm (staticCoefficient N γ))
    (contDiffOn_coefficientForm (contDiffOn_staticCoefficient hN hγ))
    (fun z hz v w => by
      rw [coefficientForm_apply, coefficientForm_apply, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
        rw [staticCoefficient_symm (hsymm _ hz) i k]
        ring)
    (fun z hz => by
      have h0 := hN0 _ hz
      rw [coefficientForm_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero, staticCoefficient_zero_zero, mul_one,
        LorentzConvention.timeSign_timeNegative]
      have : 0 < N (spatialPoint z) ^ 2 := by positivity
      linarith)
    (fun z hz v hv => by
      rw [coefficientForm_apply, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, Finset.sum_const_zero, zero_add,
        Fin.sum_univ_succ (n := n + 1), mul_zero, staticCoefficient_succ_succ,
        LorentzConvention.timeSign_timeNegative, neg_neg, one_mul]
      have h := hpos _ hz v hv
      simpa only [mul_assoc] using h)

/-- The coefficients of the static metric are the static coefficients. -/
theorem coefficient_staticMetric (V : Opens (Fin (n + 1) → ℝ)) (hN : ContDiffOn ℝ ∞ N V)
    (hγ : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hN0 : ∀ x ∈ V, N x ≠ 0)
    (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α)
    (hpos : ∀ x ∈ V, ∀ v : Fin (n + 1) → ℝ, v ≠ 0 → 0 < ∑ α, ∑ β, γ x α β * v α * v β) :
    (staticMetric N γ V hN hγ hN0 hsymm hpos).coefficient = staticCoefficient N γ := by
  funext z
  exact Matrix.ext fun i k => coefficientForm_single _ z i k

/-! ### Instances -/

/-- The identity spatial metric is positive definite. -/
theorem one_spatial_pos (v : Fin (n + 1) → ℝ) (hv : v ≠ 0) :
    0 < ∑ α, ∑ β, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) α β * v α * v β := by
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  obtain ⟨α, hα⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun β _ => mul_self_nonneg (v β))
    ⟨α, Finset.mem_univ α, mul_self_pos.mpr hα⟩

variable (n) in
/-- The Minkowski metric as static data: `N = 1`, `γ = 1`, on all of space-time. -/
def minkowskiStatic : CoordinateMetric .timeNegative (n + 1) (staticDomain ⊤) :=
  staticMetric (fun _ => 1) (fun _ => 1) ⊤ contDiffOn_const (fun _ _ => contDiffOn_const)
    (fun _ _ => one_ne_zero) (fun _ _ α β => by simp [Matrix.one_apply, eq_comm])
    (fun _ _ v hv => one_spatial_pos v hv)

variable (n) in
/-- The static metric `−e^{2x¹} dt² + Σ (dx^α)²` with the nonconstant lapse `N = e^{x¹}`, on
all of space-time. -/
def expLapseStatic : CoordinateMetric .timeNegative (n + 1) (staticDomain ⊤) :=
  staticMetric (fun x => Real.exp (x 0)) (fun _ => 1) ⊤
    (Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0)).contDiffOn
    (fun _ _ => contDiffOn_const) (fun _ _ => (Real.exp_pos _).ne')
    (fun _ _ α β => by simp [Matrix.one_apply, eq_comm])
    (fun _ _ v hv => one_spatial_pos v hv)

/-- The derivative of `e^{x¹}` along `v` is `e^{x¹} v¹`. -/
theorem fderiv_exp_apply_zero (y v : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun x : Fin (n + 1) → ℝ => Real.exp (x 0)) y v = Real.exp (y 0) * v 0 := by
  rw [((hasFDerivAt_apply 0 y).exp).fderiv]
  simp

/-- The data `N = e^{x¹}`, `γ = 1` are regular static data on all of space. -/
theorem isStaticRegularOn_expLapse :
    IsStaticRegularOn (fun x : Fin (n + 1) → ℝ => Real.exp (x 0))
      (fun _ => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) univ :=
  ⟨isOpen_univ,
    (Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0)).contDiffOn,
    fun _ _ => contDiffOn_const, fun _ _ => (Real.exp_pos _).ne', fun _ _ => by simp,
    fun _ _ α β => by simp [Matrix.one_apply, eq_comm]⟩

/-- **A nonconstant instance of the Ricci formula**: for `N = e^{x¹}` and `γ = 1`,
`Δ_γ N = e^{x¹}` and `R₀₀ = N Δ_γ N = e^{2x¹}`. -/
theorem ricciOf_expLapseStatic_zero_zero (z : MinkowskiModel (n + 1)) :
    ricciOf (expLapseStatic n).coefficient z 0 0 = Real.exp (2 * z 1) := by
  rw [expLapseStatic, coefficient_staticMetric,
    ricciOf_staticCoefficient_zero_zero isStaticRegularOn_expLapse (mem_univ _)]
  have hd (β : Fin (n + 1)) :
      (fun y => fderiv ℝ (fun x : Fin (n + 1) → ℝ => Real.exp (x 0)) y (Pi.single β 1)) =
        fun y => (Pi.single β (1 : ℝ) : Fin (n + 1) → ℝ) 0 * Real.exp (y 0) := by
    funext y
    rw [fderiv_exp_apply_zero, mul_comm]
  have hdd (α β : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
      fderiv ℝ (fun y => fderiv ℝ (fun x : Fin (n + 1) → ℝ => Real.exp (x 0)) y
        (Pi.single β 1)) x (Pi.single α 1) =
        (Pi.single β (1 : ℝ) : Fin (n + 1) → ℝ) 0 *
          (Real.exp (x 0) * (Pi.single α (1 : ℝ) : Fin (n + 1) → ℝ) 0) := by
    rw [hd, fderiv_const_mul ((hasFDerivAt_apply 0 x).exp.differentiableAt), smul_apply,
      smul_eq_mul, fderiv_exp_apply_zero]
  simp only [spatialLaplacian, christoffelOf_const, zero_mul, Finset.sum_const_zero,
    sub_zero, inv_one, hdd, Matrix.one_apply, Pi.single_apply, spatialPoint_apply]
  simp [Fin.succ_zero_eq_one, ← Real.exp_add, two_mul]

/-! ### The trace-reversed Einstein equations -/

/-- The trace `g^{ac} T_{ac}` with the static inverse: `−T₀₀ / N² + γ^{αβ} T_{αβ}`. -/
theorem staticCoefficient_inv_trace {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
    (hγ : (γ (spatialPoint z)).det ≠ 0) (T : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ) :
    ∑ a, ∑ c, (staticCoefficient N γ z)⁻¹ a c * T a c =
      -T 0 0 / N (spatialPoint z) ^ 2 +
        ∑ α, ∑ β, (γ (spatialPoint z))⁻¹ α β * T α.succ β.succ := by
  rw [staticCoefficient_inv hN hγ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (n := n + 1)]
  simp [staticInverse]
  ring

/-- **The trace-reversed Einstein equations** in four dimensions: `G_{ik} = κ T_{ik}` gives
`R_{ik} = κ (T_{ik} − ½ g_{ik} g^{ac} T_{ac})`. -/
theorem IsEinstein.ricciOf_eq {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}
    {g : CoordinateMetric σ 3 U} {κ : ℝ} {T : MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ}
    (hE : g.IsEinstein κ 0 T) {x : MinkowskiModel 3} (hx : x ∈ U) (i k : Fin 4) :
    ricciOf g.coefficient x i k =
      κ * (T x i k - g.coefficient x i k *
        (∑ a, ∑ c, (g.coefficient x)⁻¹ a c * T x a c) / 2) := by
  have h (a c : Fin 4) : ricciOf g.coefficient x a c -
      scalarOf g.coefficient x / 2 * g.coefficient x a c = κ * T x a c := by
    have := hE x hx a c
    rwa [einsteinOf, zero_mul, add_zero] at this
  have htr : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * g.coefficient x a c = 4 := by
    have hC := g.coefficient_mul_inv ⟨x, hx⟩
    have h1 : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * g.coefficient x a c =
        Matrix.trace (g.coefficient x * (g.coefficient x)⁻¹) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [g.coefficient_inv_symmetric hx a c, mul_comm]
    rw [h1, hC, Matrix.trace_one]
    simp
  have hS : scalarOf g.coefficient x =
      -(κ * ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * T x a c) := by
    have hsum : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * (ricciOf g.coefficient x a c -
        scalarOf g.coefficient x / 2 * g.coefficient x a c) =
        ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * (κ * T x a c) := by
      simp only [h]
    have hR : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * ricciOf g.coefficient x a c =
        scalarOf g.coefficient x := by
      simp only [scalarOf, mul_comm]
    have hG : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c *
        (scalarOf g.coefficient x / 2 * g.coefficient x a c) =
        scalarOf g.coefficient x / 2 * 4 := by
      rw [← htr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    have hT : ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * (κ * T x a c) =
        κ * ∑ a, ∑ c, (g.coefficient x)⁻¹ a c * T x a c := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    rw [hR, hG, hT] at hsum
    linarith
  have hik := h i k
  rw [hS] at hik
  linarith

end ProjectAinos.SmoothGeometry.CoordinateMetric

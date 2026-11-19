/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildEquatorial
public import ProjectAinos.GeneralRelativity.SchwarzschildCircular
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import ProjectAinos.SmoothAlgebra.FreeCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Chart geodesics of the geodesic Hamiltonian and native geodesics

The geodesic Hamiltonian `H = ½ g^{μν} p_μ p_ν` (`GeodesicHamiltonian`) is stated in a chart whose
coefficients `g_{μν}` are elements of the free C∞-ring, and its trajectories are the curves of
smooth functions of the affine parameter that solve the lowered geodesic equation
`g_{μν} ẍ^ν + Γ_{μαβ} ẋ^α ẋ^β = 0` (`IsCoordinateGeodesic`). This file compares them with the
native geodesics of a Lorentz manifold (Landau–Lifshitz, §87, equation (87.3), and §101).

* `isCoordinateGeodesic_iff_isGeodesicOn`: for a coordinate metric `g` on the whole model space
  whose coefficients are the values of the elements `gm μ ν`, a curve `x` solves the lowered
  equation of `gm` exactly when `τ ↦ x(τ)` (`coordinateCurve`) is a native geodesic of `g` for
  all values of the parameter. The two equations differ by the invertible matrix of
  coefficients, `Γ^k_{ij} = g^{kl} Γ_{lij}` (`christoffelOf_eq_sum_christoffelLower`).
* `SchwarzschildEquatorial.equatorialMetric`: the metric `−(eˢ/r) dt² + eˢ r ds² + r² dφ²`,
  `r = 2M + eˢ`, of the equatorial plane of the exterior Schwarzschild field as a coordinate
  metric on all of `ℝ³`; its coefficients are the values of `SchwarzschildEquatorial.metric`
  (`coefficient_equatorialMetric`).
* `SchwarzschildEquatorial.isCoordinateGeodesic_iff`,
  `SchwarzschildEquatorial.isTrajectory_iff_isGeodesicOn`: the trajectories of the geodesic
  Hamiltonian of the equatorial plane are the native geodesics of `equatorialMetric` that are
  defined for all values of the parameter, with `p_μ = g_{μν} ẋ^ν`, which is the native pairing
  `g(∂_μ, γ̇)` (`momentum_apply`).
* `isGeodesicOn_circularCurve`, `isTrajectory_circular`: for `b² r³ = M a²` the curve
  `τ ↦ (a τ, s₀, b τ)` is a native geodesic and, with constant momenta, a trajectory: Kepler's
  third law `(dφ/dt)² = M/r³` holds exactly in the co-ordinate time, at every radius `r > 2M`.
  Its squared velocity is `a² (3M − r)/r` (`form_curveVelocity_circularCurve`), so it is the
  orbit of a particle for `r > 3M`, a ray at `r = 3M` and spacelike for `2M < r < 3M`;
  `isTrajectory_kepler` is the instance `a = 1`, `b = √(M/r³)` at every radius.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian

open SmoothAlgebra SmoothRing FreeSmoothRing Mechanics SmoothGeometry
open Set TopologicalSpace
open scoped ContDiff Matrix

variable {d : ℕ}

/-- The curve `τ ↦ (x^μ(τ))` of the model space, in the chart `⊤`. -/
def coordinateCurve (x : Fin (d + 1) → TimeFunction) (τ : ℝ) :
    (⊤ : Opens (MinkowskiModel d)) :=
  ⟨fun μ => x μ (fun _ => τ), trivial⟩

/-- The co-ordinates of `coordinateCurve x τ` are the values `x^μ(τ)`. -/
theorem coordinateCurve_val (x : Fin (d + 1) → TimeFunction) (τ : ℝ) :
    (coordinateCurve x τ : MinkowskiModel d) = fun μ => x μ (fun _ => τ) := rfl

/-- The co-ordinates of `coordinateCurve x` are smooth functions of the parameter. -/
theorem contDiff_coordinateCurve (x : Fin (d + 1) → TimeFunction) :
    ContDiff ℝ ∞ (fun τ => (coordinateCurve x τ : MinkowskiModel d)) :=
  contDiff_pi.mpr fun μ => TimeFunction.contDiff_apply_const (x μ)

/-- The derivative of the co-ordinates of `coordinateCurve x` is the curve of the derivatives
`ẋ^μ = timeDerivative (x μ)`. -/
theorem deriv_coordinateCurve (x : Fin (d + 1) → TimeFunction) :
    deriv (fun τ => (coordinateCurve x τ : MinkowskiModel d)) =
      fun τ => (coordinateCurve (fun μ => timeDerivative (x μ)) τ : MinkowskiModel d) := by
  funext τ
  simp only [coordinateCurve_val]
  rw [deriv_pi fun μ => ((TimeFunction.contDiff_apply_const (x μ)).differentiable
    (by simp)).differentiableAt]
  funext μ
  exact (TimeFunction.timeDerivative_apply (x μ) τ).symm

/-- The substitution `lift x s` of the curve into an element `s` of the free ring has the value
`s(x(τ))` at the parameter `τ`. -/
theorem lift_apply_coordinateCurve (x : Fin (d + 1) → TimeFunction)
    (s : FreeSmoothRing (Fin (d + 1))) (τ : ℝ) :
    lift x s (fun _ => τ) = s.val (coordinateCurve x τ : MinkowskiModel d) := by
  have h := map_lift (SmoothOperation.eval (fun _ : Fin 1 => τ)) x s
  rw [SmoothOperation.eval_apply] at h
  rw [h, lift_real]
  rfl

/-- The partial derivation `∂_a s` of the free ring is the Fréchet derivative of `s` along the
co-ordinate axis `a`. -/
theorem val_partialDerivation (a : Fin (d + 1)) (s : FreeSmoothRing (Fin (d + 1)))
    (z : MinkowskiModel d) :
    (partialDerivation a s).val z =
      fderiv ℝ (s.val : MinkowskiModel d → ℝ) z (Pi.single a 1) := by
  rw [fderiv_val_apply]
  simp [Pi.single_apply]

/-- The values of the Christoffel symbols of the first kind of `gm` are
`½ (∂_α g_{μβ} + ∂_β g_{μα} − ∂_μ g_{αβ})`, with the Fréchet derivatives of the values. -/
theorem val_christoffelLower (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (μ α β : Fin (d + 1)) (z : MinkowskiModel d) :
    (christoffelLower gm μ α β).val z = 1 / 2 *
      (fderiv ℝ ((gm μ β).val : MinkowskiModel d → ℝ) z (Pi.single α 1) +
        fderiv ℝ ((gm μ α).val : MinkowskiModel d → ℝ) z (Pi.single β 1) -
        fderiv ℝ ((gm α β).val : MinkowskiModel d → ℝ) z (Pi.single μ 1)) := by
  rw [← lift_real, christoffelLower, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    SmoothRingHom.map_sub, SmoothRingHom.map_add, lift_real, lift_real, lift_real,
    val_partialDerivation, val_partialDerivation, val_partialDerivation]
  rfl

/-- The lowered equation `C a + Q = 0` and the raised equation `a + C⁻¹ Q = 0` are equivalent
for an invertible matrix `C`. -/
private theorem lowered_iff_raised {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℝ)
    (hC : C * C⁻¹ = 1) (a v : n → ℝ) (Γ : n → n → n → ℝ) :
    (∀ μ, ∑ ν, C μ ν * a ν + ∑ α, ∑ β, Γ μ α β * (v α * v β) = 0) ↔
      ∀ k, a k + ∑ i, ∑ j, (∑ l, C⁻¹ k l * Γ l i j) * v i * v j = 0 := by
  have hC' : C⁻¹ * C = 1 := mul_eq_one_comm.mp hC
  set Q : n → ℝ := fun l => ∑ α, ∑ β, Γ l α β * (v α * v β) with hQ
  have hR (k : n) : a k + ∑ i, ∑ j, (∑ l, C⁻¹ k l * Γ l i j) * v i * v j =
      (C⁻¹ *ᵥ (C *ᵥ a + Q)) k := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hC', Matrix.one_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, hQ, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hL (μ : n) : ∑ ν, C μ ν * a ν + ∑ α, ∑ β, Γ μ α β * (v α * v β) = (C *ᵥ a + Q) μ := rfl
  simp only [hR, hL]
  constructor
  · intro h k
    rw [show C *ᵥ a + Q = 0 from funext h, Matrix.mulVec_zero]
    rfl
  · intro h μ
    rw [← Matrix.one_mulVec (C *ᵥ a + Q), ← hC, ← Matrix.mulVec_mulVec,
      show C⁻¹ *ᵥ (C *ᵥ a + Q) = 0 from funext h, Matrix.mulVec_zero]
    rfl

variable {σ : LorentzConvention}

/-- The Christoffel symbols of a coordinate metric whose coefficients are the values of `gm` are
`Γ^k_{ij} = C^{kl} Γ_{lij}`, with the symbols `christoffelLower gm` of the first kind. -/
theorem christoffelOf_eq_sum_christoffelLower
    (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (g : CoordinateMetric σ d ⊤) (hg : ∀ y μ ν, g.coefficient y μ ν = (gm μ ν).val y)
    (y : MinkowskiModel d) (k i j : Fin (d + 1)) :
    CoordinateMetric.christoffelOf g.coefficient y k i j =
      ∑ l, (g.coefficient y)⁻¹ k l * (christoffelLower gm l i j).val y := by
  have hfun (μ ν : Fin (d + 1)) : (fun z => g.coefficient z μ ν) = (gm μ ν).val :=
    funext fun z => hg z μ ν
  have hsymm (μ ν : Fin (d + 1)) : ((gm μ ν).val : MinkowskiModel d → ℝ) = (gm ν μ).val :=
    funext fun z => by rw [← hg, ← hg, g.coefficient_symmetric trivial]
  simp only [CoordinateMetric.christoffelOf, hfun, val_christoffelLower]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsymm j l]
  ring

/-- **Chart geodesics are native geodesics.** Let `g` be a coordinate metric on the whole model
space whose coefficients are the values of the elements `gm μ ν` of the free ring. A curve
`x` of smooth functions of the parameter satisfies the lowered geodesic equation
`g_{μν} ẍ^ν + Γ_{μαβ} ẋ^α ẋ^β = 0` of `gm` exactly when the curve `τ ↦ x(τ)` is a geodesic of
the Lorentz manifold of `g` for all values of the parameter. -/
theorem isCoordinateGeodesic_iff_isGeodesicOn
    (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (g : CoordinateMetric σ d ⊤) (hg : ∀ y μ ν, g.coefficient y μ ν = (gm μ ν).val y)
    (x : Fin (d + 1) → TimeFunction) :
    IsCoordinateGeodesic gm x ↔ g.toLorentzMetric.IsGeodesicOn univ (coordinateCurve x) := by
  rw [g.isGeodesicOn_iff isOpen_univ ((contDiff_coordinateCurve x).of_le (by simp)).contDiffOn,
    deriv_coordinateCurve, deriv_coordinateCurve]
  have heval (μ : Fin (d + 1)) (τ : ℝ) :
      (∑ ν, lift x (gm μ ν) * timeDerivative (timeDerivative (x ν)) +
        ∑ α, ∑ β, lift x (christoffelLower gm μ α β) *
          (timeDerivative (x α) * timeDerivative (x β))) (fun _ => τ) =
      ∑ ν, g.coefficient (coordinateCurve x τ) μ ν *
          (coordinateCurve (fun μ => timeDerivative (timeDerivative (x μ))) τ :
            MinkowskiModel d) ν +
        ∑ α, ∑ β, (christoffelLower gm μ α β).val (coordinateCurve x τ) *
          ((coordinateCurve (fun μ => timeDerivative (x μ)) τ : MinkowskiModel d) α *
            (coordinateCurve (fun μ => timeDerivative (x μ)) τ : MinkowskiModel d) β) := by
    rw [← SmoothOperation.eval_apply (fun _ : Fin 1 => τ)]
    simp only [SmoothRingHom.map_add, SmoothRingHom.map_sum, SmoothRingHom.map_mul,
      SmoothOperation.eval_apply, lift_apply_coordinateCurve, hg]
    rfl
  have hall : IsCoordinateGeodesic gm x ↔ ∀ τ : ℝ, ∀ μ : Fin (d + 1),
      (∑ ν, lift x (gm μ ν) * timeDerivative (timeDerivative (x ν)) +
        ∑ α, ∑ β, lift x (christoffelLower gm μ α β) *
          (timeDerivative (x α) * timeDerivative (x β))) (fun _ => τ) = 0 := by
    constructor
    · intro h τ μ
      rw [h μ]
      rfl
    · intro h μ
      exact TimeFunction.ext_apply_const fun τ => h τ μ
  rw [hall]
  simp only [heval, mem_univ, true_imp_iff, christoffelOf_eq_sum_christoffelLower gm g hg]
  exact forall_congr' fun τ => lowered_iff_raised _ (g.coefficient_mul_inv _) _ _ _

/-- The lowered velocity `g_{μν}(x) ẋ^ν` at the parameter `τ` is the native pairing
`g(∂_μ, γ̇)` of the co-ordinate vector `∂_μ` with the velocity of the curve. -/
theorem sum_lift_mul_timeDerivative_apply
    (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (g : CoordinateMetric σ d ⊤) (hg : ∀ y μ ν, g.coefficient y μ ν = (gm μ ν).val y)
    (x : Fin (d + 1) → TimeFunction) (μ : Fin (d + 1)) (τ : ℝ) :
    (∑ ν, lift x (gm μ ν) * timeDerivative (x ν)) (fun _ => τ) =
      g.toLorentzMetric.form (coordinateCurve x τ)
        (LorentzMetric.chartField (CoordinateMetric.physicalChart (coordinateCurve x τ))
          (Pi.single μ 1) (coordinateCurve x τ))
        (LorentzMetric.curveVelocity (coordinateCurve x) τ) := by
  rw [g.pairing_curveVelocity (((contDiff_coordinateCurve x).differentiable
    (by simp)).differentiableAt), deriv_coordinateCurve, ← SmoothOperation.eval_apply]
  conv_rhs => rw [Finset.sum_eq_single μ (fun i _ hi => by simp [hi]) (by simp)]
  simp only [SmoothRingHom.map_sum, SmoothRingHom.map_mul, SmoothOperation.eval_apply,
    lift_apply_coordinateCurve, hg, Pi.single_eq_same, mul_one]
  rfl

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics SmoothGeometry
open Set TopologicalSpace
open scoped ContDiff

variable {M : ℝ}

/-- The real coefficients `(−eˢ/r, eˢ r, r²)` of the metric at the point `y = (t, s, φ)`. -/
def diagonalCoefficient (hM : 0 ≤ M) (y : MinkowskiModel 2) : Fin 3 → ℝ :=
  fun μ => lowerOp hM μ (fun _ => y 1)

/-- The time coefficient `−eˢ/r`. -/
theorem diagonalCoefficient_zero (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    diagonalCoefficient hM y 0 = -(Real.exp (y 1) / radius M (y 1)) := rfl

/-- The radial coefficient `eˢ r`. -/
theorem diagonalCoefficient_one (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    diagonalCoefficient hM y 1 = Real.exp (y 1) * radius M (y 1) := rfl

/-- The angular coefficient `r²`. -/
theorem diagonalCoefficient_two (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    diagonalCoefficient hM y 2 = radius M (y 1) ^ 2 := rfl

/-- The coefficients are smooth on all of `ℝ³`. -/
theorem contDiff_diagonalCoefficient (hM : 0 ≤ M) (μ : Fin 3) :
    ContDiff ℝ ∞ (fun y => diagonalCoefficient hM y μ) :=
  (lowerOp hM μ).contMDiff.contDiff.comp
    (contDiff_pi.mpr fun _ => contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 1)

/-- The metric `−(eˢ/r) dt² + eˢ r ds² + r² dφ²` of the equatorial plane, `r = 2M + eˢ`, as a
coordinate metric on the whole model space `(t, s, φ)`. -/
def equatorialMetric (hM : 0 ≤ M) : CoordinateMetric .timeNegative 2 ⊤ :=
  CoordinateMetric.ofDiagonal (diagonalCoefficient hM)
    (fun μ => (contDiff_diagonalCoefficient hM μ).contDiffOn)
    (fun y _ => by
      rw [diagonalCoefficient_zero, LorentzConvention.timeSign_timeNegative]
      have := div_pos (Real.exp_pos (y 1)) (radius_pos hM (y 1))
      linarith)
    (fun y _ α => by
      rw [LorentzConvention.timeSign_timeNegative, neg_neg, one_mul]
      fin_cases α
      · exact mul_pos (Real.exp_pos _) (radius_pos hM _)
      · exact pow_pos (radius_pos hM _) 2)

/-- The coefficients of `equatorialMetric` are the values of the free-ring metric `metric`. -/
theorem coefficient_equatorialMetric (hM : 0 ≤ M) (y : MinkowskiModel 2) (μ ν : Fin 3) :
    (equatorialMetric hM).coefficient y μ ν = (metric hM μ ν).val y := by
  rw [equatorialMetric, CoordinateMetric.coefficient_ofDiagonal, metric,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · rfl

/-- Along a curve, the lifted coefficients of `metric` are the coefficients of
`equatorialMetric` at the point of the curve. -/
theorem lift_metric_apply (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (μ ν : Fin 3) (τ : ℝ) :
    lift x (metric hM μ ν) (fun _ => τ) =
      (equatorialMetric hM).coefficient (coordinateCurve x τ) μ ν := by
  rw [lift_apply_coordinateCurve, coefficient_equatorialMetric]

/-- **The chart geodesics are the native geodesics.** A curve of smooth functions of the
parameter solves the lowered geodesic equation of `metric` exactly when it is a geodesic of the
Lorentz manifold of `equatorialMetric` for all values of the parameter. -/
theorem isCoordinateGeodesic_iff (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) :
    IsCoordinateGeodesic (metric hM) x ↔
      (equatorialMetric hM).toLorentzMetric.IsGeodesicOn univ (coordinateCurve x) :=
  isCoordinateGeodesic_iff_isGeodesicOn _ _ (coefficient_equatorialMetric hM) x

/-- **The trajectories of the geodesic Hamiltonian are native geodesics.** A curve of the phase
space is a trajectory of `H = ½ g^{μν} p_μ p_ν` exactly when `p_μ = g_{μν} ẋ^ν` and its
positions form a geodesic of the Lorentz manifold of `equatorialMetric`, defined for all values
of the affine parameter. -/
theorem isTrajectory_iff_isGeodesicOn (hM : 0 ≤ M) (c : Fin 3 ⊕ Fin 3 → TimeFunction) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c ↔
      (∀ μ, c (Sum.inr μ) =
        ∑ ν, lift (position c) (metric hM μ ν) * timeDerivative (position c ν)) ∧
        (equatorialMetric hM).toLorentzMetric.IsGeodesicOn univ
          (coordinateCurve (position c)) := by
  rw [isTrajectory_iff hM, isCoordinateGeodesic_iff hM]

/-- Along a trajectory the momentum `p_μ` is the native pairing `g(∂_μ, γ̇)` of the
co-ordinate vector `∂_μ` with the velocity of the geodesic. -/
theorem momentum_apply (hM : 0 ≤ M) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c) (μ : Fin 3) (τ : ℝ) :
    c (Sum.inr μ) (fun _ => τ) =
      (equatorialMetric hM).toLorentzMetric.form (coordinateCurve (position c) τ)
        (LorentzMetric.chartField
          (CoordinateMetric.physicalChart (coordinateCurve (position c) τ))
          (Pi.single μ 1) (coordinateCurve (position c) τ))
        (LorentzMetric.curveVelocity (coordinateCurve (position c)) τ) := by
  rw [((isTrajectory_iff hM c).mp h).1 μ]
  exact sum_lift_mul_timeDerivative_apply _ _ (coefficient_equatorialMetric hM) _ μ τ

/-! ### Circular orbits -/

/-- The derivative of a coefficient along a co-ordinate axis: the coefficients depend on `s`
only. -/
private theorem fderiv_diagonalCoefficient (hM : 0 ≤ M) (y : MinkowskiModel 2) (k i : Fin 3) :
    fderiv ℝ (fun z => diagonalCoefficient hM z k) y (Pi.single i 1) =
      deriv (fun s => lowerOp hM k (fun _ => s)) (y 1) *
        (Pi.single i 1 : MinkowskiModel 2) 1 := by
  have hf : DifferentiableAt ℝ (fun s => lowerOp hM k (fun _ => s)) (y 1) :=
    ((TimeFunction.contDiff_apply_const (lowerOp hM k)).differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun z : MinkowskiModel 2 => z 1)
      (ContinuousLinearMap.proj 1 : MinkowskiModel 2 →L[ℝ] ℝ) y := hasFDerivAt_apply 1 y
  have h := hf.hasDerivAt.comp_hasFDerivAt y h1
  rw [show (fun z => diagonalCoefficient hM z k) =
    (fun s => lowerOp hM k (fun _ => s)) ∘ fun z : MinkowskiModel 2 => z 1 from rfl, h.fderiv]
  simp

/-- `∂_s(−eˢ/r) = −2M eˢ/r²`. -/
private theorem deriv_lowerOp_zero (hM : 0 ≤ M) (s : ℝ) :
    deriv (fun s => lowerOp hM 0 (fun _ => s)) s = -(2 * M * Real.exp s / radius M s ^ 2) := by
  have hr := (radius_pos hM s).ne'
  have h : HasDerivAt (fun s => -(Real.exp s / radius M s))
      (-((Real.exp s * radius M s - Real.exp s * Real.exp s) / radius M s ^ 2)) s :=
    ((Real.hasDerivAt_exp s).div ((Real.hasDerivAt_exp s).const_add (2 * M)) hr).neg
  rw [show (fun s => lowerOp hM 0 (fun _ => s)) = fun s => -(Real.exp s / radius M s) from rfl,
    h.deriv]
  unfold radius
  ring

/-- `∂_s r² = 2 r eˢ`. -/
private theorem deriv_lowerOp_two (hM : 0 ≤ M) (s : ℝ) :
    deriv (fun s => lowerOp hM 2 (fun _ => s)) s = 2 * radius M s * Real.exp s := by
  have h : HasDerivAt (fun s => radius M s ^ 2) (↑2 * radius M s ^ (2 - 1) * Real.exp s) s :=
    ((Real.hasDerivAt_exp s).const_add (2 * M)).pow 2
  rw [show (fun s => lowerOp hM 2 (fun _ => s)) = fun s => radius M s ^ 2 from rfl, h.deriv]
  norm_num

/-- No coefficient vanishes. -/
theorem diagonalCoefficient_ne_zero (hM : 0 ≤ M) (y : MinkowskiModel 2) (μ : Fin 3) :
    diagonalCoefficient hM y μ ≠ 0 := by
  have hr := radius_pos hM (y 1)
  have he := Real.exp_pos (y 1)
  fin_cases μ
  · exact neg_ne_zero.mpr (div_pos he hr).ne'
  · exact (mul_pos he hr).ne'
  · exact (pow_pos hr 2).ne'

/-- The circular curve `τ ↦ (a τ, s₀, b τ)`, as smooth functions of the parameter. -/
def circularCurve (s₀ a b : ℝ) : Fin 3 → TimeFunction :=
  ![SmoothOperation.ofContDiff (fun t => a * t 0) (contDiff_const.mul (contDiff_apply ℝ _ 0)),
    SmoothOperation.ofContDiff (fun _ => s₀) contDiff_const,
    SmoothOperation.ofContDiff (fun t => b * t 0) (contDiff_const.mul (contDiff_apply ℝ _ 0))]

/-- The co-ordinates of the circular curve are the affine line `(0, s₀, 0) + τ (a, 0, b)`. -/
theorem coordinateCurve_circularCurve (s₀ a b τ : ℝ) :
    (coordinateCurve (circularCurve s₀ a b) τ : MinkowskiModel 2) =
      ![0, s₀, 0] + τ • ![a, 0, b] := by
  funext μ
  fin_cases μ <;> simp [coordinateCurve, circularCurve, mul_comm]

/-- **Circular orbits: a regression instance.** For `b² r³ = M a²` with `r = 2M + e^{s₀}`, the
curve `τ ↦ (a τ, s₀, b τ)` is a native geodesic of the equatorial plane: Kepler's third law
`(dφ/dt)² = M/r³` in the co-ordinate time, for every radius `r > 2M`. -/
theorem isGeodesicOn_circularCurve (hM : 0 ≤ M) {s₀ a b : ℝ}
    (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) :
    (equatorialMetric hM).toLorentzMetric.IsGeodesicOn univ
      (coordinateCurve (circularCurve s₀ a b)) := by
  refine SchwarzschildExterior.isGeodesicOn_univ_of_line _ _ _
    (coordinateCurve_circularCurve s₀ a b) fun t k => ?_
  have hy : (coordinateCurve (circularCurve s₀ a b) t : MinkowskiModel 2) 1 = s₀ := by
    rw [coordinateCurve_circularCurve]
    simp
  have hr := (radius_pos hM s₀).ne'
  have he := (Real.exp_pos s₀).ne'
  rw [equatorialMetric]
  simp only [CoordinateMetric.christoffelOf_ofDiagonal _ _ _ _ _
    (diagonalCoefficient_ne_zero hM _), fderiv_diagonalCoefficient, hy]
  fin_cases k <;>
    simp [Fin.sum_univ_three, deriv_lowerOp_zero, deriv_lowerOp_two, diagonalCoefficient_one, hy]
  field_simp
  linear_combination (-1 : ℝ) * h

/-- The circular curve solves the lowered geodesic equation of the free-ring metric. -/
theorem isCoordinateGeodesic_circularCurve (hM : 0 ≤ M) {s₀ a b : ℝ}
    (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) :
    IsCoordinateGeodesic (metric hM) (circularCurve s₀ a b) :=
  (isCoordinateGeodesic_iff hM _).mpr (isGeodesicOn_circularCurve hM h)

/-- The value of a sum of products of smooth functions of time. -/
private theorem sum_mul_apply (f g : Fin 3 → TimeFunction) (p : Fin 1 → ℝ) :
    (∑ ν, f ν * g ν) p = ∑ ν, f ν p * g ν p := by
  rw [← SmoothOperation.eval_apply p, SmoothRingHom.map_sum]
  simp only [SmoothRingHom.map_mul, SmoothOperation.eval_apply]

/-- The velocity `(a, 0, b)` of the circular curve. -/
private theorem timeDerivative_circularCurve_apply (s₀ a b τ : ℝ) (ν : Fin 3) :
    timeDerivative (circularCurve s₀ a b ν) (fun _ => τ) = ![a, 0, b] ν := by
  have h := congrFun (deriv_coordinateCurve (circularCurve s₀ a b)) τ
  have hd : HasDerivAt (fun τ : ℝ => (![0, s₀, 0] : MinkowskiModel 2) + τ • ![a, 0, b])
      ![a, 0, b] τ := by
    simpa using ((hasDerivAt_id τ).smul_const (![a, 0, b] : MinkowskiModel 2)).const_add
      (![0, s₀, 0] : MinkowskiModel 2)
  rw [show (fun τ => (coordinateCurve (circularCurve s₀ a b) τ : MinkowskiModel 2)) =
      fun τ => ![0, s₀, 0] + τ • ![a, 0, b] from funext (coordinateCurve_circularCurve s₀ a b),
    hd.deriv] at h
  exact (congrFun h ν).symm

/-- **A circular trajectory of the geodesic Hamiltonian.** For `b² r³ = M a²`, the curve
`τ ↦ (a τ, s₀, b τ)` with the constant momenta `p = (−(eˢ⁰/r) a, 0, r² b)` is a trajectory of
`H = ½ g^{μν} p_μ p_ν`; for `a ≠ 0` it is a proved instance of the trajectory hypothesis with a
nonzero velocity in the curved metric. -/
theorem isTrajectory_circular (hM : 0 ≤ M) {s₀ a b : ℝ}
    (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM))
      (Sum.elim (circularCurve s₀ a b) fun μ => algebraMap ℝ TimeFunction
        (![-(Real.exp s₀ / radius M s₀) * a, 0, radius M s₀ ^ 2 * b] μ)) := by
  refine (isTrajectory_iff_isGeodesicOn hM _).mpr ⟨fun μ => ?_, isGeodesicOn_circularCurve hM h⟩
  refine TimeFunction.ext_apply_const fun τ => ?_
  have hy : (coordinateCurve (circularCurve s₀ a b) τ : MinkowskiModel 2) 1 = s₀ := by
    rw [coordinateCurve_circularCurve]
    simp
  change _ = (∑ ν, lift (circularCurve s₀ a b) (metric hM μ ν) *
    timeDerivative (circularCurve s₀ a b ν)) (fun _ => τ)
  rw [sum_mul_apply]
  simp only [lift_metric_apply, timeDerivative_circularCurve_apply, equatorialMetric,
    CoordinateMetric.coefficient_ofDiagonal, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hc (r : ℝ) : algebraMap ℝ TimeFunction r (fun _ => τ) = r := by
    rw [← SmoothOperation.eval_apply, SmoothRingHom.map_algebraMap]
    rfl
  rw [Sum.elim_inr, hc]
  fin_cases μ <;> simp [diagonalCoefficient_zero, diagonalCoefficient_two, hy]

/-- The squared velocity of the circular curve, `g(γ̇, γ̇) = a² (3M − r)/r` for `b² r³ = M a²`:
the curve is timelike for `r > 3M`, null at `r = 3M` and spacelike for `2M < r < 3M`. -/
theorem form_curveVelocity_circularCurve (hM : 0 ≤ M) {s₀ a b : ℝ}
    (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) (τ : ℝ) :
    (equatorialMetric hM).toLorentzMetric.form (coordinateCurve (circularCurve s₀ a b) τ)
        (LorentzMetric.curveVelocity (coordinateCurve (circularCurve s₀ a b)) τ)
        (LorentzMetric.curveVelocity (coordinateCurve (circularCurve s₀ a b)) τ) =
      a ^ 2 * (3 * M - radius M s₀) / radius M s₀ := by
  have hy : (coordinateCurve (circularCurve s₀ a b) τ : MinkowskiModel 2) 1 = s₀ := by
    rw [coordinateCurve_circularCurve]
    simp
  have hv (ν : Fin 3) : deriv (fun τ => (coordinateCurve (circularCurve s₀ a b) τ :
      MinkowskiModel 2)) τ ν = ![a, 0, b] ν := by
    rw [deriv_coordinateCurve]
    exact timeDerivative_circularCurve_apply s₀ a b τ ν
  rw [(equatorialMetric hM).form_curveVelocity (((contDiff_coordinateCurve _).differentiable
    (by simp)).differentiableAt)]
  simp only [hv, equatorialMetric, CoordinateMetric.coefficient_ofDiagonal, Matrix.diagonal_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [Fin.sum_univ_three, diagonalCoefficient_zero, diagonalCoefficient_two, hy]
  have hr := (radius_pos hM s₀).ne'
  have hR : Real.exp s₀ = radius M s₀ - 2 * M := by unfold radius; ring
  rw [hR]
  field_simp
  linear_combination h

/-- The hypothesis of the circular curves is met at every radius: `a = 1` and
`b = √(M/r³)`, with `r = 2M + e^{s₀}`. -/
theorem kepler_sq (hM : 0 ≤ M) (s₀ : ℝ) :
    Real.sqrt (M / radius M s₀ ^ 3) ^ 2 * radius M s₀ ^ 3 = M * 1 ^ 2 := by
  have hr := pow_pos (radius_pos hM s₀) 3
  rw [Real.sq_sqrt (div_nonneg hM hr.le), div_mul_cancel₀ _ hr.ne', one_pow, mul_one]

/-- **Kepler's circular orbits are trajectories.** At every `s₀`, the curve
`τ ↦ (τ, s₀, √(M/r³) τ)` with constant momenta is a trajectory of the geodesic Hamiltonian:
a proved instance of `isTrajectory_circular`. -/
theorem isTrajectory_kepler (hM : 0 ≤ M) (s₀ : ℝ) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM))
      (Sum.elim (circularCurve s₀ 1 (Real.sqrt (M / radius M s₀ ^ 3))) fun μ =>
        algebraMap ℝ TimeFunction (![-(Real.exp s₀ / radius M s₀) * 1, 0,
          radius M s₀ ^ 2 * Real.sqrt (M / radius M s₀ ^ 3)] μ)) :=
  isTrajectory_circular hM (kepler_sq hM s₀)

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial


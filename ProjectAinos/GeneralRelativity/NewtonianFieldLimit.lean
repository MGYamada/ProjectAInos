/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Static
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Newton's law from the static field equations

Landau–Lifshitz, §99, for static weak fields, with `κ = 8πG`, `c = 1` and the Newtonian
parameter `ε = 1/c²`. Unlike §81 (`NewtonianMetricFamily`), the metric is not prescribed: the
potential is constrained by the field equations.

A static weak-field family (`StaticWeakFieldFamily G V`) on an open set `V` of space has, for
`ε ∈ (0, ε₀]`, the static lapse `N_ε = 1 + εΦ_ε` (`weakLapse`) and spatial metric
`γ_ε = δ + εq_ε` (`weakSpatial`), a density `ρ_ε` and a spatial stress trace `τ_ε = O(ε²)`; one
constant `K` bounds `Φ_ε`, `∂Φ_ε`, `∂²Φ_ε`, `q_ε`, `∂q_ε` and `ρ_ε`; and the time component of
the trace-reversed Einstein equations holds, `R₀₀ = 8πG (T₀₀ − ½ g₀₀ g^{ab} T_{ab})` with
`T₀₀ = ερ_ε N_ε²` and `g^{ab} T_{ab} = −ερ_ε + τ_ε`.

* `flatLaplacian_sub_eq`: **Newton's equation with an explicit remainder**. For
  `0 < ε ≤ ε₁ = min(ε₀, 1/(6(K + 1)))` (`smallParameter`), `Σ_α ∂_α² Φ_ε − 4πG ρ_ε = ε R_ε` on
  `V`, with `R_ε = γ^{αμ} q_{μβ} ∂_α∂_βΦ + γ^{αβ} Q^μ_{αβ} ∂_μΦ + 4πG (Φρ + N τ/ε²)`
  (`remainder`), where `γ^{αβ}` is the inverse of `δ + εq` and `Q = Γ̃/ε`
  (`correctionChristoffel`). The identity is derived from `R₀₀ = N Δ_γ N`
  (`ricciOf_staticCoefficient_zero_zero`).
* `inv_one_add_bound`: `1 + E` with `|E_{ij}| ≤ 1/6` is invertible, and the entries of its
  inverse are at most `2`.
* `abs_remainder_le`, `abs_flatLaplacian_sub_le`: **the Poisson limit at the rate `O(ε)`**,
  `|Σ_α ∂_α² Φ_ε − 4πG ρ_ε| ≤ C ε` on `V` for `0 < ε ≤ ε₁`, with the explicit constant
  `C = 540 K² + 4πG (K² + 2P)` (`errorConstant`), for `G ≥ 0`.
* `flatLaplacian_eq_of_tendsto`: if the second derivatives `∂_α² Φ_ε(x)` and the densities
  `ρ_ε(x)` converge as `ε → 0⁺`, the limits satisfy `ΔΦ(x) = 4πG ρ(x)`.
* `fieldEquation_of_isEinstein`: the full Einstein equations `G_{ik} = 8πG T_{ik}` of a static
  coordinate metric with a comoving source `T₀₀ = ερN²`, `γ^{αβ} T_{αβ} = τ` give the field
  equation of the family (by the trace reversal `IsEinstein.ricciOf_eq`).
* Instances: `StaticWeakFieldFamily.trivialFamily` (Minkowski space, `Φ = 0`, `q = 0`, `ρ = 0`) and
  `StaticWeakFieldFamily.halfSquare`: on the open cube `|x^α| < 1`, `Φ = (x¹)²/2`, `q = 0`,
  `τ = 0` and the density `ρ_ε = 1/(4πG(1 + εΦ))`, defined from the field so that the field
  equation holds exactly; it is positive, and in the limit it gives Poisson's equation with
  the uniform density `1/(4πG)` (`halfSquare_poisson`).

Slowly varying fields, with time derivatives, are not treated here (§106).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology Matrix Real

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric

/-! ### Weak-field static data -/

/-- The weak-field lapse `N = 1 + εΦ`. -/
def weakLapse (ε : ℝ) (Φ : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ := 1 + ε * Φ x

/-- The weak-field spatial metric `γ = δ + ε q`. -/
def weakSpatial (ε : ℝ) (q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  1 + ε • q x

/-- The flat Laplacian `Σ_α ∂_α² f`. -/
def flatLaplacian (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ α, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single α 1)) x (Pi.single α 1)

/-- The entries of the weak-field spatial metric: `γ_{αβ} = δ_{αβ} + ε q_{αβ}`. -/
theorem weakSpatial_apply (ε : ℝ) (q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (x : Fin 3 → ℝ) (α β : Fin 3) :
    weakSpatial ε q x α β = (1 : Matrix (Fin 3) (Fin 3) ℝ) α β + ε * q x α β := by
  simp [weakSpatial]

/-- The derivative of the lapse: `∂N = ε ∂Φ`. -/
theorem fderiv_weakLapse {ε : ℝ} {Φ : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hΦ : DifferentiableAt ℝ Φ x) (v : Fin 3 → ℝ) :
    fderiv ℝ (weakLapse ε Φ) x v = ε * fderiv ℝ Φ x v := by
  change fderiv ℝ (fun y => 1 + ε * Φ y) x v = _
  rw [fderiv_const_add, fderiv_const_mul hΦ, smul_apply, smul_eq_mul]

/-- The second derivatives of the lapse: `∂_α ∂_β N = ε ∂_α ∂_β Φ`. -/
theorem fderiv_fderiv_weakLapse {ε : ℝ} {Φ : (Fin 3 → ℝ) → ℝ} {V : Set (Fin 3 → ℝ)}
    (hV : IsOpen V) (hΦ : ContDiffOn ℝ ∞ Φ V) {x : Fin 3 → ℝ} (hx : x ∈ V) (α β : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (weakLapse ε Φ) y (Pi.single β 1)) x (Pi.single α 1) =
      ε * fderiv ℝ (fun y => fderiv ℝ Φ y (Pi.single β 1)) x (Pi.single α 1) := by
  have hev : (fun y => fderiv ℝ (weakLapse ε Φ) y (Pi.single β 1)) =ᶠ[𝓝 x]
      fun y => ε * fderiv ℝ Φ y (Pi.single β 1) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact fderiv_weakLapse ((hΦ.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)) _
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ Φ y (Pi.single β 1)) x := by
    have h : ContDiffOn ℝ ∞ (fun y => fderiv ℝ Φ y (Pi.single β 1)) V :=
      (hΦ.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
    exact (h.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)
  rw [hev.fderiv_eq, fderiv_const_mul hd, smul_apply, smul_eq_mul]

/-- The derivative of the spatial metric: `∂γ_{αβ} = ε ∂q_{αβ}`. -/
theorem fderiv_weakSpatial {ε : ℝ} {q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {x : Fin 3 → ℝ} {α β : Fin 3} (hq : DifferentiableAt ℝ (fun y => q y α β) x)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => weakSpatial ε q y α β) x v = ε * fderiv ℝ (fun y => q y α β) x v := by
  simp only [weakSpatial_apply]
  rw [fderiv_const_add, fderiv_const_mul hq, smul_apply, smul_eq_mul]

/-- The Christoffel symbols of `γ = δ + εq` divided by `ε`:
`Q^μ_{αβ} = ½ γ^{μν} (∂_α q_{βν} + ∂_β q_{να} − ∂_ν q_{αβ})`. -/
def correctionChristoffel (ε : ℝ) (q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (x : Fin 3 → ℝ) (μ α β : Fin 3) : ℝ :=
  ∑ ν, (weakSpatial ε q x)⁻¹ μ ν *
    (fderiv ℝ (fun y => q y β ν) x (Pi.single α 1) +
      fderiv ℝ (fun y => q y ν α) x (Pi.single β 1) -
      fderiv ℝ (fun y => q y α β) x (Pi.single ν 1)) / 2

/-- The Christoffel symbols of the weak-field spatial metric are `Γ̃ = ε Q`. -/
theorem christoffelOf_weakSpatial {ε : ℝ} {q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {x : Fin 3 → ℝ} (hq : ∀ α β, DifferentiableAt ℝ (fun y => q y α β) x) (μ α β : Fin 3) :
    christoffelOf (weakSpatial ε q) x μ α β = ε * correctionChristoffel ε q x μ α β := by
  unfold christoffelOf correctionChristoffel
  simp only [fderiv_weakSpatial (hq _ _), Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- The inverse of `γ = δ + εq` satisfies `γ^{αβ} + ε γ^{αμ} q_{μβ} = δ^{αβ}`. -/
theorem inv_weakSpatial_add {ε : ℝ} {q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {x : Fin 3 → ℝ} (hdet : (weakSpatial ε q x).det ≠ 0) (α β : Fin 3) :
    (weakSpatial ε q x)⁻¹ α β + ε * ∑ μ, (weakSpatial ε q x)⁻¹ α μ * q x μ β =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) α β := by
  unfold weakSpatial at hdet ⊢
  have h := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at h
  have h' := congrFun (congrFun h α) β
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] using h'

/-! ### Small perturbations of the identity -/

/-- A sum of three terms bounded by `B` is bounded by `3B`. -/
theorem abs_sum_fin_three_le {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)
  simp

/-- A product of bounded factors is bounded by the product of the bounds. -/
theorem abs_mul_le_of_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- **The inverse of a small perturbation of the identity**: if every entry of `E` is at most
`1/6`, then `1 + E` is invertible and every entry of its inverse is at most `2`. -/
theorem inv_one_add_bound {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : ∀ i j, |E i j| ≤ 1 / 6) :
    (1 + E).det ≠ 0 ∧ ∀ i j, |(1 + E)⁻¹ i j| ≤ 2 := by
  have hmul (v : Fin 3 → ℝ) : ‖E *ᵥ v‖ ≤ 1 / 2 * ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have h := abs_sum_fin_three_le (f := fun j => E i j * v j) (B := 1 / 6 * ‖v‖)
      fun j => abs_mul_le_of_le (hE i j) (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j)
    change |∑ j, E i j * v j| ≤ _
    linarith
  have hdet : (1 + E).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hEv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hEv
    have hv' : v = -(E *ᵥ v) := eq_neg_of_add_eq_zero_left hEv
    have h1 : ‖v‖ ≤ 1 / 2 * ‖v‖ := by
      calc ‖v‖ = ‖E *ᵥ v‖ := by rw [hv', norm_neg, ← hv']
        _ ≤ 1 / 2 * ‖v‖ := hmul v
    exact hv (norm_eq_zero.mp (le_antisymm (by linarith [norm_nonneg v]) (norm_nonneg v)))
  refine ⟨hdet, fun i j => ?_⟩
  set w := (1 + E)⁻¹ *ᵥ (Pi.single j 1 : Fin 3 → ℝ) with hw
  have hEw : w + E *ᵥ w = Pi.single j 1 := by
    have h1 : (1 + E) *ᵥ w = Pi.single j 1 := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec]
    rwa [Matrix.add_mulVec, Matrix.one_mulVec] at h1
  have hwn : ‖w‖ ≤ 2 := by
    have h := norm_sub_le (Pi.single j (1 : ℝ) : Fin 3 → ℝ) (E *ᵥ w)
    rw [← hEw, add_sub_cancel_right, hEw] at h
    have hs : ‖(Pi.single j (1 : ℝ) : Fin 3 → ℝ)‖ = 1 := by
      simp [Pi.norm_single]
    linarith [hmul w]
  have hwi : w i = (1 + E)⁻¹ i j := by
    rw [hw, Matrix.mulVec_single_one]
    rfl
  rw [← hwi, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm w i).trans hwn

/-! ### Static weak-field families -/

/-- **A static weak-field family** (Landau–Lifshitz, §99) on an open set `V` of space, with
Newton's constant `G`, `κ = 8πG` and `c = 1`. For the Newtonian parameter `ε = 1/c²` in
`(0, ε₀]`, the lapse is `N_ε = 1 + εΦ_ε` and the spatial metric `γ_ε = δ + ε q_ε`, both static;
the source has the energy density `ε ρ_ε`, so `T₀₀ = ε ρ_ε N_ε²` and `g^{ab} T_{ab} = −ερ_ε + τ_ε`
with the spatial trace `τ_ε = O(ε²)`. One constant `K` bounds `Φ_ε` and its first and second
derivatives, `q_ε` and its first derivatives, and `ρ_ε`, uniformly in `ε`. The field equation
is the time component of the trace-reversed Einstein equations,
`R₀₀ = κ (T₀₀ − ½ g₀₀ g^{ab} T_{ab})` (`field_equation`); it follows from the full equations by
`fieldEquation_of_isEinstein`. -/
structure StaticWeakFieldFamily (G : ℝ) (V : Opens (Fin 3 → ℝ)) where
  /-- The largest parameter `ε₀`. -/
  maxParameter : ℝ
  /-- The parameter range is not empty. -/
  maxParameter_pos : 0 < maxParameter
  /-- The potential `Φ_ε`. -/
  potential : ℝ → (Fin 3 → ℝ) → ℝ
  /-- The correction `q_ε` of the spatial metric. -/
  spatialCorrection : ℝ → (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ
  /-- The mass density `ρ_ε`; the energy density is `ε ρ_ε`. -/
  density : ℝ → (Fin 3 → ℝ) → ℝ
  /-- The spatial trace `τ_ε = g^{αβ} T_{αβ}` of the stresses. -/
  stressTrace : ℝ → (Fin 3 → ℝ) → ℝ
  /-- The potential is smooth on `V`. -/
  potential_smooth : ∀ ε ∈ Ioc 0 maxParameter, ContDiffOn ℝ ∞ (potential ε) V
  /-- The correction of the spatial metric is smooth on `V`. -/
  correction_smooth : ∀ ε ∈ Ioc 0 maxParameter, ∀ α β,
    ContDiffOn ℝ ∞ (fun x => spatialCorrection ε x α β) V
  /-- The correction of the spatial metric is symmetric. -/
  correction_symm : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, ∀ α β,
    spatialCorrection ε x α β = spatialCorrection ε x β α
  /-- The common bound `K`. -/
  bound : ℝ
  /-- The common bound is not negative. -/
  bound_nonneg : 0 ≤ bound
  /-- `|Φ_ε| ≤ K`. -/
  potential_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, |potential ε x| ≤ bound
  /-- `|∂_α Φ_ε| ≤ K`. -/
  potential_first_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, ∀ α,
    |fderiv ℝ (potential ε) x (Pi.single α 1)| ≤ bound
  /-- `|∂_α ∂_β Φ_ε| ≤ K`. -/
  potential_second_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, ∀ α β,
    |fderiv ℝ (fun y => fderiv ℝ (potential ε) y (Pi.single β 1)) x (Pi.single α 1)| ≤ bound
  /-- `|q_{ε,αβ}| ≤ K`. -/
  correction_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, ∀ α β,
    |spatialCorrection ε x α β| ≤ bound
  /-- `|∂_μ q_{ε,αβ}| ≤ K`. -/
  correction_first_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, ∀ μ α β,
    |fderiv ℝ (fun y => spatialCorrection ε y α β) x (Pi.single μ 1)| ≤ bound
  /-- `|ρ_ε| ≤ K`. -/
  density_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V, |density ε x| ≤ bound
  /-- The bound `P` of `τ_ε / ε²`. -/
  stressBound : ℝ
  /-- `|τ_ε| ≤ ε² P`. -/
  stressTrace_le : ∀ ε ∈ Ioc 0 maxParameter, ∀ x ∈ V,
    |stressTrace ε x| ≤ ε ^ 2 * stressBound
  /-- The time component of the trace-reversed Einstein equations,
  `R₀₀ = 8πG (T₀₀ − ½ g₀₀ g^{ab} T_{ab})` with `T₀₀ = ε ρ_ε N_ε²` and
  `g^{ab} T_{ab} = −ερ_ε + τ_ε`, at every event over `V`. -/
  field_equation : ∀ ε ∈ Ioc 0 maxParameter, ∀ z : MinkowskiModel 3, spatialPoint z ∈ V →
    ricciOf (staticCoefficient (weakLapse ε (potential ε))
        (weakSpatial ε (spatialCorrection ε))) z 0 0 =
      8 * π * G * (ε * density ε (spatialPoint z) *
          weakLapse ε (potential ε) (spatialPoint z) ^ 2 -
        staticCoefficient (weakLapse ε (potential ε)) (weakSpatial ε (spatialCorrection ε)) z
            0 0 * (-(ε * density ε (spatialPoint z)) + stressTrace ε (spatialPoint z)) / 2)

namespace StaticWeakFieldFamily

variable {G : ℝ} {V : Opens (Fin 3 → ℝ)} (f : StaticWeakFieldFamily G V)

/-- The parameter bound `ε₁ = min(ε₀, 1/(6(K + 1)))` of the estimates. -/
def smallParameter : ℝ := min f.maxParameter (1 / (6 * (f.bound + 1)))

/-- `ε₁ > 0`. -/
theorem smallParameter_pos : 0 < f.smallParameter :=
  lt_min f.maxParameter_pos (by have := f.bound_nonneg; positivity)

/-- `ε₁ ≤ ε₀`. -/
theorem mem_Ioc_maxParameter {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) :
    ε ∈ Ioc 0 f.maxParameter :=
  ⟨hε.1, hε.2.trans (min_le_left _ _)⟩

/-- Below `ε₁`, `ε K ≤ 1/6`. -/
theorem mul_bound_le {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) : ε * f.bound ≤ 1 / 6 := by
  have h1 : ε ≤ 1 / (6 * (f.bound + 1)) := hε.2.trans (min_le_right _ _)
  have hK := f.bound_nonneg
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith [hε.1]

/-- Below `ε₁`, the lapse lies in `[5/6, 7/6]`. -/
theorem lapse_mem {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    5 / 6 ≤ weakLapse ε (f.potential ε) x ∧ weakLapse ε (f.potential ε) x ≤ 7 / 6 := by
  have hΦ := abs_le.mp (f.potential_le ε (f.mem_Ioc_maxParameter hε) x hx)
  have hK := f.mul_bound_le hε
  have h0 := hε.1
  unfold weakLapse
  constructor <;> nlinarith

/-- Below `ε₁`, the spatial metric is invertible and the entries of its inverse are at
most `2`. -/
theorem spatial_inv {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    (weakSpatial ε (f.spatialCorrection ε) x).det ≠ 0 ∧
      ∀ α β, |(weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β| ≤ 2 := by
  refine inv_one_add_bound fun i j => ?_
  have hq := f.correction_le ε (f.mem_Ioc_maxParameter hε) x hx i j
  have hK := f.mul_bound_le hε
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hε.1]
  nlinarith [hε.1]

/-- Below `ε₁`, the weak-field data are regular static data on `V`. -/
theorem isStaticRegularOn {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) :
    IsStaticRegularOn (weakLapse ε (f.potential ε)) (weakSpatial ε (f.spatialCorrection ε)) V := by
  have hε' := f.mem_Ioc_maxParameter hε
  refine ⟨V.isOpen, contDiffOn_const.add (contDiffOn_const.mul (f.potential_smooth ε hε')),
    fun α β => ?_, fun x hx => (lt_of_lt_of_le (by norm_num) (f.lapse_mem hε hx).1).ne',
    fun x hx => (f.spatial_inv hε hx).1, fun x hx α β => ?_⟩
  · simp only [weakSpatial_apply]
    exact contDiffOn_const.add (contDiffOn_const.mul (f.correction_smooth ε hε' α β))
  · rw [weakSpatial_apply, weakSpatial_apply, f.correction_symm ε hε' x hx α β,
      Matrix.one_apply, Matrix.one_apply]
    simp only [eq_comm]

/-- **The remainder of Newton's equation**:
`R_ε = γ^{αμ} q_{μβ} ∂_α∂_βΦ + γ^{αβ} Q^μ_{αβ} ∂_μΦ + 4πG (Φρ + N τ/ε²)`, with the inverse
`γ^{αβ}` of `γ = δ + εq` and `Q = Γ̃/ε` (`correctionChristoffel`). -/
def remainder (ε : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ α, ∑ β, (∑ μ, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α μ *
      f.spatialCorrection ε x μ β) *
      fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1) +
    ∑ α, ∑ β, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
      ∑ μ, correctionChristoffel ε (f.spatialCorrection ε) x μ α β *
        fderiv ℝ (f.potential ε) x (Pi.single μ 1) +
    4 * π * G * (f.potential ε x * f.density ε x +
      weakLapse ε (f.potential ε) x * f.stressTrace ε x / ε ^ 2)

/-- **Newton's equation with an explicit remainder**: below `ε₁`,
`Σ_α ∂_α² Φ_ε − 4πG ρ_ε = ε R_ε` on `V`. It is derived from `R₀₀ = N Δ_γ N`. -/
theorem flatLaplacian_sub_eq {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ}
    (hx : x ∈ V) :
    flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x = ε * f.remainder ε x := by
  have hε' := f.mem_Ioc_maxParameter hε
  have hε0 : ε ≠ 0 := hε.1.ne'
  have hreg := f.isStaticRegularOn hε
  have hz : spatialPoint (Fin.cons 0 x : MinkowskiModel 3) ∈ V := by
    rw [spatialPoint_cons]
    exact hx
  have hR := f.field_equation ε hε' _ hz
  rw [ricciOf_staticCoefficient_zero_zero hreg hz, staticCoefficient_zero_zero,
    spatialPoint_cons] at hR
  have hN0 : weakLapse ε (f.potential ε) x ≠ 0 := hreg.lapse_ne_zero x hx
  have hdet := (f.spatial_inv hε hx).1
  have hΦd : DifferentiableAt ℝ (f.potential ε) x :=
    ((f.potential_smooth ε hε').contDiffAt (V.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hqd (α β : Fin 3) : DifferentiableAt ℝ (fun y => f.spatialCorrection ε y α β) x :=
    (((f.correction_smooth ε hε' α β).contDiffAt (V.isOpen.mem_nhds hx))).differentiableAt
      (by simp)
  have hinner (α β : Fin 3) :
      ∑ μ, christoffelOf (weakSpatial ε (f.spatialCorrection ε)) x μ α β *
          fderiv ℝ (weakLapse ε (f.potential ε)) x (Pi.single μ 1) =
        ε ^ 2 * ∑ μ, correctionChristoffel ε (f.spatialCorrection ε) x μ α β *
          fderiv ℝ (f.potential ε) x (Pi.single μ 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [christoffelOf_weakSpatial hqd, fderiv_weakLapse hΦd]
    ring
  have hlap : spatialLaplacian (weakSpatial ε (f.spatialCorrection ε))
      (weakLapse ε (f.potential ε)) x =
      ε * ∑ α, ∑ β, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
          fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1) -
        ε ^ 2 * ∑ α, ∑ β, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
          ∑ μ, correctionChristoffel ε (f.spatialCorrection ε) x μ α β *
            fderiv ℝ (f.potential ε) x (Pi.single μ 1) := by
    have h1 : spatialLaplacian (weakSpatial ε (f.spatialCorrection ε))
        (weakLapse ε (f.potential ε)) x =
        ∑ α, ∑ β, (ε * ((weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
            fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1)) -
          ε ^ 2 * ((weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
            ∑ μ, correctionChristoffel ε (f.spatialCorrection ε) x μ α β *
              fderiv ℝ (f.potential ε) x (Pi.single μ 1))) := by
      unfold spatialLaplacian
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [fderiv_fderiv_weakLapse V.isOpen (f.potential_smooth ε hε') hx, hinner]
      ring
    rw [h1]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hflat : flatLaplacian (f.potential ε) x =
      ∑ α, ∑ β, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
          fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1) +
        ε * ∑ α, ∑ β, (∑ μ, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α μ *
          f.spatialCorrection ε x μ β) *
          fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1) := by
    have h1 (α β : Fin 3) :
        (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β *
            fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1) +
          ε * ((∑ μ, (weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α μ *
            f.spatialCorrection ε x μ β) *
            fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1)) =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) α β *
          fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x (Pi.single α 1) := by
      rw [← inv_weakSpatial_add hdet α β]
      ring
    calc flatLaplacian (f.potential ε) x =
        ∑ α, ∑ β, (1 : Matrix (Fin 3) (Fin 3) ℝ) α β *
          fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single β 1)) x
            (Pi.single α 1) := by
          simp [flatLaplacian, Matrix.one_apply]
      _ = _ := by
          simp only [← h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : weakLapse ε (f.potential ε) x *
      (spatialLaplacian (weakSpatial ε (f.spatialCorrection ε)) (weakLapse ε (f.potential ε)) x -
        4 * π * G * weakLapse ε (f.potential ε) x *
          (ε * f.density ε x + f.stressTrace ε x)) = 0 := by
    linear_combination hR
  have h3 := (mul_eq_zero.mp h2).resolve_left hN0
  rw [hlap] at h3
  rw [hflat, remainder]
  have hNdef : weakLapse ε (f.potential ε) x = 1 + ε * f.potential ε x := rfl
  rw [hNdef] at h3 ⊢
  field_simp
  linear_combination h3

/-- The explicit constant `C(K, P, G) = 540 K² + 4πG (K² + 2P)` of the estimate. -/
def errorConstant : ℝ := 540 * f.bound ^ 2 + 4 * π * G * (f.bound ^ 2 + 2 * f.stressBound)

/-- Below `ε₁`, the remainder is bounded by `C(K, P, G)` on `V`. -/
theorem abs_remainder_le (hG : 0 ≤ G) {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter)
    {x : Fin 3 → ℝ} (hx : x ∈ V) : |f.remainder ε x| ≤ f.errorConstant := by
  have hε' := f.mem_Ioc_maxParameter hε
  have hK := f.bound_nonneg
  have hg := (f.spatial_inv hε hx).2
  have hq := f.correction_le ε hε' x hx
  have hdq := f.correction_first_le ε hε' x hx
  have hdΦ := f.potential_first_le ε hε' x hx
  have hd2Φ := f.potential_second_le ε hε' x hx
  have hΦ := f.potential_le ε hε' x hx
  have hρ := f.density_le ε hε' x hx
  have hτ := f.stressTrace_le ε hε' x hx
  have hN := f.lapse_mem hε hx
  have hε2 : 0 < ε ^ 2 := pow_pos hε.1 2
  have hP : 0 ≤ f.stressBound :=
    (mul_nonneg_iff_of_pos_left hε2).mp ((abs_nonneg _).trans hτ)
  have hQ (μ α β : Fin 3) :
      |correctionChristoffel ε (f.spatialCorrection ε) x μ α β| ≤ 3 * (2 * (3 * f.bound) / 2) := by
    unfold correctionChristoffel
    refine abs_sum_fin_three_le fun ν => ?_
    have h3 : |fderiv ℝ (fun y => f.spatialCorrection ε y β ν) x (Pi.single α 1) +
        fderiv ℝ (fun y => f.spatialCorrection ε y ν α) x (Pi.single β 1) -
        fderiv ℝ (fun y => f.spatialCorrection ε y α β) x (Pi.single ν 1)| ≤ 3 * f.bound := by
      have ha := abs_le.mp (hdq α β ν)
      have hb := abs_le.mp (hdq β ν α)
      have hc := abs_le.mp (hdq ν α β)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_mul_le_of_le (hg μ ν) h3) (by norm_num)
  have hA := abs_sum_fin_three_le fun α => abs_sum_fin_three_le fun β =>
    abs_mul_le_of_le (abs_sum_fin_three_le fun μ => abs_mul_le_of_le (hg α μ) (hq μ β))
      (hd2Φ α β)
  have hB := abs_sum_fin_three_le fun α => abs_sum_fin_three_le fun β =>
    abs_mul_le_of_le (hg α β)
      (abs_sum_fin_three_le fun μ => abs_mul_le_of_le (hQ μ α β) (hdΦ μ))
  have hτε : |f.stressTrace ε x / ε ^ 2| ≤ f.stressBound := by
    rw [abs_div, abs_of_pos hε2, div_le_iff₀ hε2]
    linarith
  have hNabs : |weakLapse ε (f.potential ε) x| ≤ 2 := by
    rw [abs_of_pos (by linarith [hN.1])]
    linarith [hN.2]
  have hC : |4 * π * G * (f.potential ε x * f.density ε x +
      weakLapse ε (f.potential ε) x * f.stressTrace ε x / ε ^ 2)| ≤
      4 * π * G * (f.bound ^ 2 + 2 * f.stressBound) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * G)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := abs_mul_le_of_le hΦ hρ
    have h2 := abs_mul_le_of_le hNabs hτε
    rw [← mul_div_assoc] at h2
    linarith [abs_add_le (f.potential ε x * f.density ε x)
      (weakLapse ε (f.potential ε) x * f.stressTrace ε x / ε ^ 2), sq f.bound]
  unfold remainder errorConstant
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ _ := add_le_add_three hA hB hC
    _ = _ := by ring

/-- **The Poisson limit at the rate `O(ε)`**: for `0 < ε ≤ ε₁` and `x ∈ V`,
`|Σ_α ∂_α² Φ_ε(x) − 4πG ρ_ε(x)| ≤ C(K, P, G) ε`. -/
theorem abs_flatLaplacian_sub_le (hG : 0 ≤ G) {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter)
    {x : Fin 3 → ℝ} (hx : x ∈ V) :
    |flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x| ≤ f.errorConstant * ε := by
  rw [f.flatLaplacian_sub_eq hε hx, abs_mul, abs_of_pos hε.1, mul_comm]
  exact mul_le_mul_of_nonneg_right (f.abs_remainder_le hG hε hx) hε.1.le

/-- **The Newtonian limit**: if at a point `x ∈ V` the second derivatives `∂_α² Φ_ε(x)` and the
densities `ρ_ε(x)` converge as `ε → 0⁺` to those of `Φ` and `ρ`, then Poisson's equation
`Σ_α ∂_α² Φ(x) = 4πG ρ(x)` holds. -/
theorem flatLaplacian_eq_of_tendsto (hG : 0 ≤ G) {x : Fin 3 → ℝ} (hx : x ∈ V)
    {Φ ρ : (Fin 3 → ℝ) → ℝ}
    (hΦ : ∀ α, Tendsto (fun ε => fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single α 1))
      x (Pi.single α 1)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ (fun y => fderiv ℝ Φ y (Pi.single α 1)) x (Pi.single α 1))))
    (hρ : Tendsto (fun ε => f.density ε x) (𝓝[>] 0) (𝓝 (ρ x))) :
    flatLaplacian Φ x = 4 * π * G * ρ x := by
  have hlim : Tendsto (fun ε => flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x)
      (𝓝[>] 0) (𝓝 (flatLaplacian Φ x - 4 * π * G * ρ x)) := by
    unfold flatLaplacian
    exact (tendsto_finsetSum _ fun α _ => hΦ α).sub (hρ.const_mul _)
  have hzero : Tendsto (fun ε => flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x)
      (𝓝[>] 0) (𝓝 0) := by
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ‖flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x‖ ≤
          f.errorConstant * ε := by
      filter_upwards [Ioc_mem_nhdsGT f.smallParameter_pos] with ε hε
      rw [Real.norm_eq_abs]
      exact f.abs_flatLaplacian_sub_le hG hε hx
    have h0 : Tendsto (fun ε : ℝ => f.errorConstant * ε) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => f.errorConstant * ε) (𝓝 0)
          (𝓝 (f.errorConstant * 0)) := tendsto_id.const_mul _
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' hev h0
  have h := tendsto_nhds_unique hlim hzero
  linarith

end StaticWeakFieldFamily

/-- **The field equation from the full Einstein equations**: for a coordinate metric with static
coefficients, `G_{ik} = 8πG T_{ik}` with a comoving source `T₀₀ = ε ρ N²` and spatial trace
`γ^{αβ} T_{αβ} = τ` gives the time component of the trace-reversed equations,
`R₀₀ = 8πG (T₀₀ − ½ g₀₀ (−ερ + τ))`: the hypothesis `field_equation` of a static weak-field
family. -/
theorem fieldEquation_of_isEinstein {G : ℝ} {U : Opens (MinkowskiModel 3)}
    {g : CoordinateMetric .timeNegative 3 U} {N : (Fin 3 → ℝ) → ℝ}
    {γ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (hg : g.coefficient = staticCoefficient N γ)
    {T : MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ} (hE : g.IsEinstein (8 * π * G) 0 T)
    {z : MinkowskiModel 3} (hz : z ∈ U) (hN : N (spatialPoint z) ≠ 0)
    (hdet : (γ (spatialPoint z)).det ≠ 0) {ε ρ τ : ℝ}
    (hT : T z 0 0 = ε * ρ * N (spatialPoint z) ^ 2)
    (hτ : ∑ α, ∑ β, (γ (spatialPoint z))⁻¹ α β * T z α.succ β.succ = τ) :
    ricciOf (staticCoefficient N γ) z 0 0 =
      8 * π * G * (ε * ρ * N (spatialPoint z) ^ 2 -
        staticCoefficient N γ z 0 0 * (-(ε * ρ) + τ) / 2) := by
  have h := hE.ricciOf_eq hz 0 0
  rw [hg, staticCoefficient_inv_trace hN hdet, hτ, hT] at h
  rw [h]
  field_simp


/-! ### Instances -/

namespace StaticWeakFieldFamily

/-- **The trivial family**: Minkowski space, with `Φ = 0`, `q = 0`, `ρ = 0` and `τ = 0`. -/
def trivialFamily (G : ℝ) (V : Opens (Fin 3 → ℝ)) : StaticWeakFieldFamily G V where
  maxParameter := 1
  maxParameter_pos := one_pos
  potential _ _ := 0
  spatialCorrection _ _ := 0
  density _ _ := 0
  stressTrace _ _ := 0
  potential_smooth _ _ := contDiffOn_const
  correction_smooth _ _ _ _ := contDiffOn_const
  correction_symm _ _ _ _ _ _ := rfl
  bound := 0
  bound_nonneg := le_rfl
  potential_le _ _ _ _ := by simp
  potential_first_le _ _ _ _ _ := by simp
  potential_second_le _ _ _ _ _ _ := by simp
  correction_le _ _ _ _ _ _ := by simp
  correction_first_le _ _ _ _ _ _ _ := by simp
  density_le _ _ _ _ := by simp
  stressBound := 0
  stressTrace_le _ _ _ _ := by simp
  field_equation ε _ z _ := by
    have h : staticCoefficient (weakLapse ε fun _ => 0) (weakSpatial ε fun _ => 0) =
        fun _ => staticCoefficient (weakLapse ε fun _ => 0) (weakSpatial ε fun _ => 0) 0 :=
      funext fun _ => rfl
    rw [h, ricciOf_const]
    simp

/-! ### A family with a source -/

/-- The open cube `|x^α| < 1`, the unit ball of the sup norm. -/
def openUnitCube : Opens (Fin 3 → ℝ) := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The first co-ordinate of a point of the cube is in `(−1, 1)`. -/
theorem abs_lt_one_of_mem_openUnitCube {x : Fin 3 → ℝ} (hx : x ∈ openUnitCube) :
    |x 0| < 1 := by
  have h : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm x 0).trans_lt h

/-- The potential `Φ = (x¹)²/2`, with `ΔΦ = 1`. -/
def halfSquarePotential (x : Fin 3 → ℝ) : ℝ := x 0 ^ 2 / 2

/-- The potential `(x¹)²/2` is smooth. -/
theorem contDiff_halfSquarePotential : ContDiff ℝ ∞ halfSquarePotential :=
  ((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 0).pow 2).div_const 2

/-- `∂Φ = x¹ dx¹`. -/
theorem fderiv_halfSquarePotential (y v : Fin 3 → ℝ) :
    fderiv ℝ halfSquarePotential y v = y 0 * v 0 := by
  have h0 : HasFDerivAt (fun x : Fin 3 → ℝ => x 0)
      (ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ) y := hasFDerivAt_apply 0 y
  have h := (h0.pow 2).mul_const (1 / 2 : ℝ)
  rw [show halfSquarePotential = fun x : Fin 3 → ℝ => x 0 ^ 2 * (1 / 2) from
    funext fun x => by rw [halfSquarePotential]; ring, h.fderiv]
  simp
  ring

/-- `∂_α ∂_β Φ = δ_{α1} δ_{β1}`. -/
theorem fderiv_fderiv_halfSquarePotential (x : Fin 3 → ℝ) (α β : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ halfSquarePotential y (Pi.single β 1)) x (Pi.single α 1) =
      (Pi.single β (1 : ℝ) : Fin 3 → ℝ) 0 * (Pi.single α (1 : ℝ) : Fin 3 → ℝ) 0 := by
  have h : (fun y => fderiv ℝ halfSquarePotential y (Pi.single β 1)) =
      fun y : Fin 3 → ℝ => (Pi.single β (1 : ℝ) : Fin 3 → ℝ) 0 * y 0 := by
    funext y
    rw [fderiv_halfSquarePotential, mul_comm]
  have h0 : HasFDerivAt (fun x : Fin 3 → ℝ => x 0)
      (ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply 0 x
  rw [h, (h0.const_mul _).fderiv]
  simp

/-- The flat Laplacian of `(x¹)²/2` is `1`. -/
theorem flatLaplacian_halfSquarePotential (x : Fin 3 → ℝ) :
    flatLaplacian halfSquarePotential x = 1 := by
  simp [flatLaplacian, fderiv_fderiv_halfSquarePotential, Pi.single_apply]

/-- The density `ρ_ε = 1 / (4πG (1 + εΦ))` that solves the field equation for `Φ = (x¹)²/2`
and `γ = δ`. -/
def halfSquareDensity (G ε : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  1 / (4 * π * G * weakLapse ε halfSquarePotential x)

/-- **A family with a source** (the option of defining `ρ_ε` from the field): on the open cube,
the potential `Φ = (x¹)²/2`, the flat spatial metric `q = 0`, no stresses `τ = 0`, and the
density `ρ_ε = 1/(4πG (1 + εΦ))`, which is positive, makes `R₀₀ = 4πG ε ρ_ε N²` hold exactly,
and tends to `1/(4πG)`, so that `ΔΦ = 4πG ρ` in the limit. -/
def halfSquare (G : ℝ) (hG : 0 < G) : StaticWeakFieldFamily G openUnitCube where
  maxParameter := 1
  maxParameter_pos := one_pos
  potential _ := halfSquarePotential
  spatialCorrection _ _ := 0
  density := halfSquareDensity G
  stressTrace _ _ := 0
  potential_smooth _ _ := contDiff_halfSquarePotential.contDiffOn
  correction_smooth _ _ _ _ := contDiffOn_const
  correction_symm _ _ _ _ _ _ := rfl
  bound := 1 + 1 / (4 * π * G)
  bound_nonneg := by positivity
  potential_le _ _ x hx := by
    have h := abs_lt_one_of_mem_openUnitCube hx
    have hpos : (0 : ℝ) ≤ 1 / (4 * π * G) := by positivity
    rw [halfSquarePotential, abs_of_nonneg (by positivity)]
    nlinarith [abs_nonneg (x 0), sq_abs (x 0)]
  potential_first_le _ _ x hx α := by
    have h := abs_lt_one_of_mem_openUnitCube hx
    have hpos : (0 : ℝ) ≤ 1 / (4 * π * G) := by positivity
    rw [fderiv_halfSquarePotential, abs_mul]
    have hs : |(Pi.single α (1 : ℝ) : Fin 3 → ℝ) 0| ≤ 1 := by
      rw [Pi.single_apply]
      split_ifs <;> simp
    nlinarith [abs_nonneg (x 0), abs_nonneg ((Pi.single α (1 : ℝ) : Fin 3 → ℝ) 0)]
  potential_second_le _ _ x _ α β := by
    have hpos : (0 : ℝ) ≤ 1 / (4 * π * G) := by positivity
    rw [fderiv_fderiv_halfSquarePotential, abs_mul]
    have hs (γ : Fin 3) : |(Pi.single γ (1 : ℝ) : Fin 3 → ℝ) 0| ≤ 1 := by
      rw [Pi.single_apply]
      split_ifs <;> simp
    nlinarith [hs α, hs β, abs_nonneg ((Pi.single α (1 : ℝ) : Fin 3 → ℝ) 0),
      abs_nonneg ((Pi.single β (1 : ℝ) : Fin 3 → ℝ) 0)]
  correction_le _ _ _ _ _ _ := by
    simp only [Matrix.zero_apply, abs_zero]
    positivity
  correction_first_le _ _ _ _ _ _ _ := by
    simp only [Matrix.zero_apply, fderiv_const_apply, zero_apply, abs_zero]
    positivity
  density_le ε hε x _ := by
    have hN : 1 ≤ weakLapse ε halfSquarePotential x := by
      have : 0 ≤ ε * halfSquarePotential x := mul_nonneg hε.1.le (by
        unfold halfSquarePotential
        positivity)
      unfold weakLapse
      linarith
    have hG' : 0 < 4 * π * G := by positivity
    rw [halfSquareDensity, abs_of_pos (by positivity)]
    calc 1 / (4 * π * G * weakLapse ε halfSquarePotential x) ≤ 1 / (4 * π * G * 1) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ ≤ 1 + 1 / (4 * π * G) := by
          rw [mul_one]
          linarith
  stressBound := 0
  stressTrace_le _ _ _ _ := by simp
  field_equation ε hε z hz := by
    have hγ : weakSpatial ε (fun _ => 0) = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      funext x
      simp [weakSpatial]
    have hN (x : Fin 3 → ℝ) : 1 ≤ weakLapse ε halfSquarePotential x := by
      have : 0 ≤ ε * halfSquarePotential x := mul_nonneg hε.1.le (by
        unfold halfSquarePotential
        positivity)
      unfold weakLapse
      linarith
    have hreg : IsStaticRegularOn (weakLapse ε halfSquarePotential)
        (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) openUnitCube :=
      ⟨openUnitCube.isOpen, contDiffOn_const.add
          (contDiffOn_const.mul contDiff_halfSquarePotential.contDiffOn),
        fun _ _ => contDiffOn_const, fun x _ => (lt_of_lt_of_le one_pos (hN x)).ne',
        fun _ _ => by simp, fun _ _ α β => by simp [Matrix.one_apply, eq_comm]⟩
    rw [hγ, ricciOf_staticCoefficient_zero_zero hreg hz, staticCoefficient_zero_zero]
    have hlap : spatialLaplacian (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (weakLapse ε halfSquarePotential) (spatialPoint z) = ε := by
      unfold spatialLaplacian
      simp only [christoffelOf_const, zero_mul, Finset.sum_const_zero, sub_zero, inv_one,
        fderiv_fderiv_weakLapse openUnitCube.isOpen contDiff_halfSquarePotential.contDiffOn hz,
        fderiv_fderiv_halfSquarePotential, Matrix.one_apply, Pi.single_apply]
      simp
    rw [hlap, halfSquareDensity]
    have h1 := hN (spatialPoint z)
    have hN0 : weakLapse ε halfSquarePotential (spatialPoint z) ≠ 0 := by linarith
    have hG0 : G ≠ 0 := hG.ne'
    field_simp
    ring

/-- **The limit of the family with a source**: the hypotheses of
`flatLaplacian_eq_of_tendsto` hold for `halfSquare`, and give Poisson's equation
`Σ_α ∂_α² Φ = 4πG ρ` for `Φ = (x¹)²/2` and the uniform density `ρ = 1/(4πG)`. -/
theorem halfSquare_poisson (G : ℝ) (hG : 0 < G) {x : Fin 3 → ℝ} (hx : x ∈ openUnitCube) :
    flatLaplacian halfSquarePotential x = 4 * π * G * (fun _ => 1 / (4 * π * G)) x := by
  refine (halfSquare G hG).flatLaplacian_eq_of_tendsto (Φ := halfSquarePotential)
    (ρ := fun _ => 1 / (4 * π * G)) hG.le hx (fun α => tendsto_const_nhds.congr fun _ => rfl) ?_
  have h : Tendsto (fun ε : ℝ => 4 * π * G * weakLapse ε halfSquarePotential x) (𝓝 0)
      (𝓝 (4 * π * G * weakLapse 0 halfSquarePotential x)) := by
    unfold weakLapse
    exact ((continuous_const.mul (continuous_const.add
      (continuous_id.mul continuous_const))).tendsto 0)
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).div h (by
    simp only [weakLapse, zero_mul, add_zero, mul_one]
    positivity)
  simp only [weakLapse, zero_mul, add_zero, mul_one] at h2
  exact h2.mono_left nhdsWithin_le_nhds

end StaticWeakFieldFamily

end ProjectAinos.GeneralRelativity

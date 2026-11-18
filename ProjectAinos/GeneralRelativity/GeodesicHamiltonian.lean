/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.Trajectory
public import ProjectAinos.SmoothAlgebra.Poisson.Position
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The Hamiltonian of geodesics

In a chart whose domain is all of `ℝⁿ`, the coefficients `g_{μν}` of a metric and `g^{μν}` of
its inverse are functions of the co-ordinates, elements of the free C∞-ring, and the Hamiltonian
of geodesics is `H = ½ g^{μν}(x) p_μ p_ν` in the canonical phase space (Landau–Lifshitz,
*The Classical Theory of Fields*, §§87, 88; stage G-H of the plan).

* `canonical_q_hamiltonian`, `canonical_p_hamiltonian`: Hamilton's equations
  `ẋ^μ = g^{μν} p_ν` and `ṗ_λ = −½ ∂_λ g^{μν} p_μ p_ν`. With the metric,
  `ṗ_λ = ½ ∂_λ g_{αβ} ẋ^α ẋ^β` (`canonical_p_hamiltonian_eq`).
* `isTrajectory_iff`: a curve of the phase space is a trajectory of `H` exactly when
  `p_μ = g_{μν} ẋ^ν` and the positions satisfy the geodesic equation
  `g_{μν} ẍ^ν + Γ_{μαβ} ẋ^α ẋ^β = 0` of the chart (`IsCoordinateGeodesic`).
* `canonical_vectorMomentum_hamiltonian`: for a vector field `ξ`,
  `{ξ^μ p_μ, H} = −½ (L_ξ g⁻¹)^{μν} p_μ p_ν`, and `of_lieInverse`:
  `L_ξ g⁻¹ = −g⁻¹ (L_ξ g) g⁻¹`. So `ξ^μ p_μ` is an integral of the motion exactly when `ξ`
  satisfies the Killing equation `L_ξ g = 0` (`isIntegral_vectorMomentum_iff_killing`), and the
  momentum of a co-ordinate on which the metric does not depend is an integral
  (`isIntegral_p_of_metric_independent`).
* `pairing_eq_of_killing`: along a trajectory the pairing `g(ξ, ẋ)` of a Killing field with the
  velocity is constant. An observer who moves along a timelike Killing field `ξ` has the velocity
  `ξ/N` with `N = √(−g(ξ, ξ))` and measures the frequency `ω = −g(ξ, ẋ)/N` of a ray `x`;
  `killingNorm_mul_frequency_eq` is the red shift `N ω = const` along the ray.
* `isTrajectory_rest`, `isTrajectory_line`: the curve that rests at a point with zero momenta is
  a trajectory for every metric, and for constant coefficients every straight line with constant
  momenta is one: proved instances of the trajectory hypothesis.

The statements are about the trajectories of `H`: curves defined for all values of the affine
parameter, in a chart whose domain is all of `ℝⁿ`. A geodesic that leaves the chart at a finite
parameter is not a trajectory; the red shift along a given geodesic segment of a Lorentz
manifold is `LorentzMetric.killingNorm_mul_observedFrequency_eq`. A chart with singular
coefficients is not an instance.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `½ · 2 = 1` in a real algebra. -/
private theorem algebraMap_half_mul_two {A : Type*} [Ring A] [Algebra ℝ A] :
    algebraMap ℝ A (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap ℝ A) 2, ← map_mul]
  norm_num

/-! ### The Hamiltonian and its brackets -/

/-- The quadratic function `F^{μν}(x) p_μ p_ν` of the momenta. -/
def quadratic (F : ι → ι → FreeSmoothRing ι) : PhaseSpace ι :=
  ∑ μ, ∑ ν, ofPosition ι (F μ ν) * (p μ * p ν)

/-- The Hamiltonian `½ g^{μν}(x) p_μ p_ν` of the inverse metric `gi`. -/
def hamiltonian (gi : ι → ι → FreeSmoothRing ι) : PhaseSpace ι :=
  algebraMap ℝ (PhaseSpace ι) (1 / 2) * quadratic gi

/-- The momentum `ξ^μ p_μ` of a vector field. -/
def vectorMomentum (ξ : ι → FreeSmoothRing ι) : PhaseSpace ι := ∑ μ, ofPosition ι (ξ μ) * p μ

/-- The velocity `g^{μν} p_ν`. -/
def velocity (gi : ι → ι → FreeSmoothRing ι) (μ : ι) : PhaseSpace ι := vectorMomentum (gi μ)

/-- The derivative `(L_ξ g⁻¹)^{μν} = ξ^λ ∂_λ g^{μν} − g^{λν} ∂_λ ξ^μ − g^{μλ} ∂_λ ξ^ν` of the
inverse metric along a vector field. -/
def lieInverse (ξ : ι → FreeSmoothRing ι) (gi : ι → ι → FreeSmoothRing ι) (μ ν : ι) :
    FreeSmoothRing ι :=
  ∑ l, (ξ l * partialDerivation l (gi μ ν) - gi l ν * partialDerivation l (ξ μ) -
    gi μ l * partialDerivation l (ξ ν))

/-- `{x^b, ξ^μ p_μ} = ξ^b`. -/
theorem canonical_q_vectorMomentum (ξ : ι → FreeSmoothRing ι) (b : ι) :
    (canonical ι).bracket (q b) (vectorMomentum ξ) = ofPosition ι (ξ b) := by
  have h (μ : ι) : (canonical ι).bracket (q b) (ofPosition ι (ξ μ) * p μ) =
      if b = μ then ofPosition ι (ξ μ) else 0 := by
    rw [AlmostPoissonStructure.bracket_mul_right, canonical_q_p, canonical_q_ofPosition]
    split_ifs <;> ring
  rw [vectorMomentum, AlmostPoissonStructure.bracket_sum_right]
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- `{x^a, F^{μν} p_μ p_ν} = F^{μa} p_μ + F^{aν} p_ν`. -/
theorem canonical_q_quadratic (F : ι → ι → FreeSmoothRing ι) (a : ι) :
    (canonical ι).bracket (q a) (quadratic F) =
      vectorMomentum (fun μ => F μ a) + vectorMomentum (F a) := by
  have h (μ ν : ι) : (canonical ι).bracket (q a) (ofPosition ι (F μ ν) * (p μ * p ν)) =
      (if a = ν then ofPosition ι (F μ ν) * p μ else 0) +
        (if a = μ then ofPosition ι (F μ ν) * p ν else 0) := by
    rw [AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_mul_right,
      canonical_q_p, canonical_q_p, canonical_q_ofPosition]
    split_ifs <;> ring
  rw [quadratic, AlmostPoissonStructure.bracket_sum_right]
  simp only [AlmostPoissonStructure.bracket_sum_right, h, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, vectorMomentum]
  · rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, vectorMomentum]

/-- `{p_l, F^{μν} p_μ p_ν} = −∂_l F^{μν} p_μ p_ν`. -/
theorem canonical_p_quadratic (F : ι → ι → FreeSmoothRing ι) (l : ι) :
    (canonical ι).bracket (p l) (quadratic F) =
      -quadratic (fun μ ν => partialDerivation l (F μ ν)) := by
  have h (μ ν : ι) : (canonical ι).bracket (p l) (ofPosition ι (F μ ν) * (p μ * p ν)) =
      -(ofPosition ι (partialDerivation l (F μ ν)) * (p μ * p ν)) := by
    rw [AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_mul_right,
      canonical_p_p, canonical_p_p, canonical_p_ofPosition]
    ring
  rw [quadratic, AlmostPoissonStructure.bracket_sum_right]
  simp only [AlmostPoissonStructure.bracket_sum_right, h, Finset.sum_neg_distrib, quadratic]

/-- The bracket of a momentum with one term of a quadratic function. -/
theorem canonical_vectorMomentum_term (ξ : ι → FreeSmoothRing ι) (f : FreeSmoothRing ι)
    (α β : ι) :
    (canonical ι).bracket (vectorMomentum ξ) (ofPosition ι f * (p α * p β)) =
      -∑ l, ofPosition ι (ξ l * partialDerivation l f) * (p α * p β) +
        (∑ μ, ofPosition ι (f * partialDerivation α (ξ μ)) * (p μ * p β) +
          ∑ μ, ofPosition ι (f * partialDerivation β (ξ μ)) * (p α * p μ)) := by
  have h (μ : ι) : (canonical ι).bracket (ofPosition ι (ξ μ) * p μ)
      (ofPosition ι f * (p α * p β)) =
      -(ofPosition ι (ξ μ * partialDerivation μ f) * (p α * p β)) +
        (ofPosition ι (f * partialDerivation α (ξ μ)) * (p μ * p β) +
          ofPosition ι (f * partialDerivation β (ξ μ)) * (p α * p μ)) := by
    rw [AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_right,
      AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_mul_right,
      AlmostPoissonStructure.bracket_mul_right, canonical_p_p, canonical_p_p,
      canonical_p_ofPosition, canonical_ofPosition_p, canonical_ofPosition_p,
      canonical_ofPosition_ofPosition, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
      SmoothRingHom.map_mul]
    ring
  rw [vectorMomentum, AlmostPoissonStructure.bracket_sum_left]
  simp only [h, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- `{ξ^μ p_μ, F^{μν} p_μ p_ν} = −(L_ξ F)^{μν} p_μ p_ν`. -/
theorem canonical_vectorMomentum_quadratic (ξ : ι → FreeSmoothRing ι)
    (F : ι → ι → FreeSmoothRing ι) :
    (canonical ι).bracket (vectorMomentum ξ) (quadratic F) = -quadratic (lieInverse ξ F) := by
  have h2 : ∑ α, ∑ β, ∑ μ, ofPosition ι (F α β * partialDerivation α (ξ μ)) * (p μ * p β) =
      ∑ μ, ∑ ν, ∑ l, ofPosition ι (F l ν * partialDerivation l (ξ μ)) * (p μ * p ν) :=
    calc ∑ α, ∑ β, ∑ μ, ofPosition ι (F α β * partialDerivation α (ξ μ)) * (p μ * p β)
        = ∑ α, ∑ μ, ∑ β, ofPosition ι (F α β * partialDerivation α (ξ μ)) * (p μ * p β) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ μ, ∑ α, ∑ β, ofPosition ι (F α β * partialDerivation α (ξ μ)) * (p μ * p β) :=
          Finset.sum_comm
      _ = ∑ μ, ∑ β, ∑ α, ofPosition ι (F α β * partialDerivation α (ξ μ)) * (p μ * p β) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h3 : ∑ α, ∑ β, ∑ μ, ofPosition ι (F α β * partialDerivation β (ξ μ)) * (p α * p μ) =
      ∑ μ, ∑ ν, ∑ l, ofPosition ι (F μ l * partialDerivation l (ξ ν)) * (p μ * p ν) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hL (μ ν : ι) : ofPosition ι (lieInverse ξ F μ ν) * (p μ * p ν) =
      ∑ l, ofPosition ι (ξ l * partialDerivation l (F μ ν)) * (p μ * p ν) -
        ∑ l, ofPosition ι (F l ν * partialDerivation l (ξ μ)) * (p μ * p ν) -
        ∑ l, ofPosition ι (F μ l * partialDerivation l (ξ ν)) * (p μ * p ν) := by
    rw [lieInverse, Finset.sum_sub_distrib, Finset.sum_sub_distrib, SmoothRingHom.map_sub,
      SmoothRingHom.map_sub, SmoothRingHom.map_sum, SmoothRingHom.map_sum,
      SmoothRingHom.map_sum, sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [quadratic, AlmostPoissonStructure.bracket_sum_right]
  simp only [AlmostPoissonStructure.bracket_sum_right, canonical_vectorMomentum_term,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, quadratic, hL, Finset.sum_sub_distrib, h2, h3]
  abel

variable {gi gm : ι → ι → FreeSmoothRing ι}

/-- Hamilton's equation for a position: `ẋ^μ = {x^μ, H} = g^{μν} p_ν`. -/
theorem canonical_q_hamiltonian (hs : ∀ μ ν, gi μ ν = gi ν μ) (a : ι) :
    (canonical ι).bracket (q a) (hamiltonian gi) = velocity gi a := by
  have hsym : vectorMomentum (fun μ => gi μ a) = velocity gi a := by
    rw [velocity]
    congr 1
    funext μ
    exact hs μ a
  rw [hamiltonian, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero, canonical_q_quadratic,
    hsym, ← velocity, ← two_mul, ← mul_assoc, algebraMap_half_mul_two, one_mul]

/-- Hamilton's equation for a momentum: `ṗ_l = {p_l, H} = −½ ∂_l g^{μν} p_μ p_ν`. -/
theorem canonical_p_hamiltonian (l : ι) :
    (canonical ι).bracket (p l) (hamiltonian gi) =
      -(algebraMap ℝ (PhaseSpace ι) (1 / 2) *
        quadratic (fun μ ν => partialDerivation l (gi μ ν))) := by
  rw [hamiltonian, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero, canonical_p_quadratic]
  ring

/-- `{ξ^μ p_μ, H} = −½ (L_ξ g⁻¹)^{μν} p_μ p_ν`. -/
theorem canonical_vectorMomentum_hamiltonian (ξ : ι → FreeSmoothRing ι) :
    (canonical ι).bracket (vectorMomentum ξ) (hamiltonian gi) =
      -(algebraMap ℝ (PhaseSpace ι) (1 / 2) * quadratic (lieInverse ξ gi)) := by
  rw [hamiltonian, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero,
    canonical_vectorMomentum_quadratic]
  ring

/-! ### Integrals of the motion -/

/-- The coefficients of a quadratic function are recovered by two brackets with positions. -/
theorem canonical_q_q_quadratic (F : ι → ι → FreeSmoothRing ι) (a b : ι) :
    (canonical ι).bracket (q b) ((canonical ι).bracket (q a) (quadratic F)) =
      ofPosition ι (F b a + F a b) := by
  rw [canonical_q_quadratic, AlmostPoissonStructure.bracket_add_right, canonical_q_vectorMomentum,
    canonical_q_vectorMomentum, SmoothRingHom.map_add]

theorem lieInverse_symm (hs : ∀ μ ν, gi μ ν = gi ν μ) (ξ : ι → FreeSmoothRing ι) (μ ν : ι) :
    lieInverse ξ gi μ ν = lieInverse ξ gi ν μ := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hs ν μ, hs l μ, hs ν l]
  ring

/-- `ξ^μ p_μ` is an integral of the motion if `L_ξ g⁻¹ = 0`. -/
theorem isIntegral_vectorMomentum_of_lieInverse {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieInverse ξ gi μ ν = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) := by
  rw [PoissonStructure.IsIntegral, canonical_vectorMomentum_hamiltonian]
  simp [quadratic, hξ]

/-- `ξ^μ p_μ` is an integral of the motion exactly when `L_ξ g⁻¹ = 0`;
`isIntegral_vectorMomentum_iff_killing` is the statement with the Killing equation `L_ξ g = 0`. -/
theorem isIntegral_vectorMomentum_iff (hs : ∀ μ ν, gi μ ν = gi ν μ) (ξ : ι → FreeSmoothRing ι) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) ↔
      ∀ μ ν, lieInverse ξ gi μ ν = 0 := by
  refine ⟨fun h a b => ?_, isIntegral_vectorMomentum_of_lieInverse⟩
  rw [PoissonStructure.IsIntegral, canonical_vectorMomentum_hamiltonian, neg_eq_zero] at h
  have hQ : quadratic (lieInverse ξ gi) = 0 := by
    have h2 := congrArg (fun y => 2 * y) h
    simp only [mul_zero] at h2
    rw [← mul_assoc, mul_comm 2, algebraMap_half_mul_two, one_mul] at h2
    exact h2
  have hb := canonical_q_q_quadratic (lieInverse ξ gi) a b
  rw [hQ, AlmostPoissonStructure.bracket_zero_right, AlmostPoissonStructure.bracket_zero_right,
    ← SmoothRingHom.map_zero (ofPosition ι), lieInverse_symm hs ξ b a] at hb
  have h2 : (2 : FreeSmoothRing ι) * lieInverse ξ gi a b = 0 := by
    rw [two_mul]
    exact (ofPosition_injective hb).symm
  calc lieInverse ξ gi a b
      = algebraMap ℝ (FreeSmoothRing ι) (1 / 2) * 2 * lieInverse ξ gi a b := by
        rw [algebraMap_half_mul_two, one_mul]
    _ = 0 := by rw [mul_assoc, h2, mul_zero]

/-- The momentum of a co-ordinate on which the inverse metric does not depend is an integral of
the motion; `isIntegral_p_of_metric_independent` is the statement for the metric. -/
theorem isIntegral_p_of_independent {k : ι} (h : ∀ μ ν, partialDerivation k (gi μ ν) = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (p k) := by
  rw [PoissonStructure.IsIntegral, canonical_p_hamiltonian]
  simp [quadratic, h]

/-! ### Co-ordinate fields -/

/-- The co-ordinate vector field `∂_k`. -/
def coordinateField (k : ι) : ι → FreeSmoothRing ι := fun μ => if μ = k then 1 else 0

/-- The momentum of `∂_k` is `p_k`. -/
theorem vectorMomentum_coordinateField (k : ι) : vectorMomentum (coordinateField k) = p k := by
  simp only [vectorMomentum, coordinateField, apply_ite (ofPosition ι), SmoothRingHom.map_one,
    SmoothRingHom.map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-- `L_{∂_k} g⁻¹ = ∂_k g⁻¹`. -/
theorem lieInverse_coordinateField (k : ι) (gi : ι → ι → FreeSmoothRing ι) (μ ν : ι) :
    lieInverse (coordinateField k) gi μ ν = partialDerivation k (gi μ ν) := by
  have h0 (μ l : ι) : partialDerivation l (coordinateField k μ) = 0 := by
    unfold coordinateField
    split_ifs
    · exact SmoothDerivation.map_one _
    · exact map_zero _
  simp only [lieInverse, h0, mul_zero, sub_zero]
  simp only [coordinateField, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-! ### The Killing equation of the metric -/

/-- The Lie derivative `(L_ξ g)_{μν} = ξ^λ ∂_λ g_{μν} + g_{λν} ∂_μ ξ^λ + g_{μλ} ∂_ν ξ^λ`. -/
def lieMetric (ξ : ι → FreeSmoothRing ι) (gm : ι → ι → FreeSmoothRing ι) (μ ν : ι) :
    FreeSmoothRing ι :=
  ∑ l, (ξ l * partialDerivation l (gm μ ν) + gm l ν * partialDerivation μ (ξ l) +
    gm μ l * partialDerivation ν (ξ l))

/-- The derivative of a matrix of functions, entry by entry. -/
def matrixDeriv (l : ι) (M : Matrix ι ι (FreeSmoothRing ι)) : Matrix ι ι (FreeSmoothRing ι) :=
  M.map (partialDerivation l)

theorem matrixDeriv_mul (l : ι) (M N : Matrix ι ι (FreeSmoothRing ι)) :
    matrixDeriv l (M * N) = matrixDeriv l M * N + M * matrixDeriv l N := by
  refine Matrix.ext fun i j => ?_
  simp only [matrixDeriv, Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    SmoothDerivation.map_mul, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => mul_comm _ _) rfl

omit [Fintype ι] in
theorem matrixDeriv_one (l : ι) : matrixDeriv l (1 : Matrix ι ι (FreeSmoothRing ι)) = 0 := by
  refine Matrix.ext fun i j => ?_
  simp only [matrixDeriv, Matrix.map_apply, Matrix.one_apply, Matrix.zero_apply]
  split_ifs
  · exact SmoothDerivation.map_one _
  · exact map_zero _

/-- `L_ξ g⁻¹ = −g⁻¹ (L_ξ g) g⁻¹`, as matrices. -/
theorem of_lieInverse (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (ξ : ι → FreeSmoothRing ι) :
    Matrix.of (lieInverse ξ gi) = -(Matrix.of gi * Matrix.of (lieMetric ξ gm) * Matrix.of gi) := by
  let G : Matrix ι ι (FreeSmoothRing ι) := Matrix.of gm
  let K : Matrix ι ι (FreeSmoothRing ι) := Matrix.of gi
  let A : Matrix ι ι (FreeSmoothRing ι) := Matrix.of fun μ l => partialDerivation l (ξ μ)
  have hGK : G * K = 1 := Matrix.ext fun μ ν => by
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv μ ν
  have hKG : K * G = 1 := mul_eq_one_comm.mp hGK
  have hDK (l : ι) : matrixDeriv l K = -(K * matrixDeriv l G * K) := by
    have h := matrixDeriv_mul l K G
    rw [hKG, matrixDeriv_one] at h
    calc matrixDeriv l K = matrixDeriv l K * (G * K) := by rw [hGK, Matrix.mul_one]
      _ = (matrixDeriv l K * G) * K := by rw [Matrix.mul_assoc]
      _ = (-(K * matrixDeriv l G)) * K := by rw [eq_neg_of_add_eq_zero_left h.symm]
      _ = _ := by rw [Matrix.neg_mul, Matrix.mul_assoc]
  have hLI : Matrix.of (lieInverse ξ gi) =
      ∑ l, ξ l • matrixDeriv l K - A * K - K * A.transpose := by
    refine Matrix.ext fun μ ν => ?_
    simp only [lieInverse, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
      matrixDeriv, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      smul_eq_mul, K, A, Finset.sum_sub_distrib]
    congr 1
    exact congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  have hLG : Matrix.of (lieMetric ξ gm) =
      ∑ l, ξ l • matrixDeriv l G + A.transpose * G + G * A := by
    refine Matrix.ext fun μ ν => ?_
    simp only [lieMetric, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      matrixDeriv, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      smul_eq_mul, G, A, Finset.sum_add_distrib]
    congr 1
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  have h1 : K * (∑ l, ξ l • matrixDeriv l G) * K = ∑ l, ξ l • (-matrixDeriv l K) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hDK l, neg_neg]
  have h2 : K * (A.transpose * G) * K = K * A.transpose := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGK, Matrix.mul_one]
  have h3 : K * (G * A) * K = A * K := by
    rw [← Matrix.mul_assoc, hKG, Matrix.one_mul]
  change Matrix.of (lieInverse ξ gi) = -(K * Matrix.of (lieMetric ξ gm) * K)
  rw [hLI, hLG, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, h1, h2, h3]
  simp only [smul_neg, Finset.sum_neg_distrib]
  abel

/-- `L_ξ g = −g (L_ξ g⁻¹) g`, as matrices. -/
theorem of_lieMetric (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (ξ : ι → FreeSmoothRing ι) :
    Matrix.of (lieMetric ξ gm) = -(Matrix.of gm * Matrix.of (lieInverse ξ gi) * Matrix.of gm) := by
  have hGK : (Matrix.of gm * Matrix.of gi : Matrix ι ι (FreeSmoothRing ι)) = 1 :=
    Matrix.ext fun μ ν => by
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hinv μ ν
  have hKG : (Matrix.of gi * Matrix.of gm : Matrix ι ι (FreeSmoothRing ι)) = 1 :=
    mul_eq_one_comm.mp hGK
  rw [of_lieInverse hinv ξ, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hGK, Matrix.one_mul, Matrix.mul_assoc, hKG, Matrix.mul_one]

/-- The two forms of the Killing equation agree: `L_ξ g⁻¹ = 0` exactly when `L_ξ g = 0`. -/
theorem lieInverse_eq_zero_iff (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (ξ : ι → FreeSmoothRing ι) :
    (∀ μ ν, lieInverse ξ gi μ ν = 0) ↔ ∀ μ ν, lieMetric ξ gm μ ν = 0 := by
  constructor
  · intro h μ ν
    have h0 : Matrix.of (lieInverse ξ gi) = 0 := Matrix.ext fun μ ν => h μ ν
    have := congrArg (fun M : Matrix ι ι (FreeSmoothRing ι) => M μ ν) (of_lieMetric hinv ξ)
    simpa [h0] using this
  · intro h μ ν
    have h0 : Matrix.of (lieMetric ξ gm) = 0 := Matrix.ext fun μ ν => h μ ν
    have := congrArg (fun M : Matrix ι ι (FreeSmoothRing ι) => M μ ν) (of_lieInverse hinv ξ)
    simpa [h0] using this

/-- `L_{∂_k} g = ∂_k g`. -/
theorem lieMetric_coordinateField (k : ι) (gm : ι → ι → FreeSmoothRing ι) (μ ν : ι) :
    lieMetric (coordinateField k) gm μ ν = partialDerivation k (gm μ ν) := by
  have h0 (μ l : ι) : partialDerivation l (coordinateField k μ) = 0 := by
    unfold coordinateField
    split_ifs
    · exact SmoothDerivation.map_one _
    · exact map_zero _
  simp only [lieMetric, h0, mul_zero, add_zero]
  simp only [coordinateField, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-! ### The metric and the velocity -/

/-- The inverse matrix is also a left inverse. -/
theorem inverse_mul (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (μ ν : ι) :
    ∑ l, gi μ l * gm l ν = if μ = ν then 1 else 0 := by
  have h : (Matrix.of gm * Matrix.of gi : Matrix ι ι (FreeSmoothRing ι)) = 1 :=
    Matrix.ext fun μ ν => by
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hinv μ ν
  have h' : (Matrix.of gi * Matrix.of gm : Matrix ι ι (FreeSmoothRing ι)) μ ν =
      (1 : Matrix ι ι (FreeSmoothRing ι)) μ ν := by
    rw [mul_eq_one_comm.mp h]
  rw [Matrix.mul_apply, Matrix.one_apply] at h'
  exact h'

/-- The inverse of a symmetric matrix is symmetric. -/
theorem inverse_symm (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (μ ν : ι) :
    gi μ ν = gi ν μ := by
  let G : Matrix ι ι (FreeSmoothRing ι) := Matrix.of gm
  let K : Matrix ι ι (FreeSmoothRing ι) := Matrix.of gi
  have hGK : G * K = 1 := Matrix.ext fun μ ν => by
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv μ ν
  have hG : G.transpose = G := Matrix.ext fun μ ν => hm ν μ
  have hK : K.transpose = K :=
    calc K.transpose = K.transpose * (G * K) := by rw [hGK, Matrix.mul_one]
      _ = (G * K).transpose * K := by rw [Matrix.transpose_mul, hG, Matrix.mul_assoc]
      _ = K := by rw [hGK, Matrix.transpose_one, Matrix.one_mul]
  exact congrArg (fun M : Matrix ι ι (FreeSmoothRing ι) => M ν μ) hK

/-- `ξ^μ p_μ` is an integral of the motion if `ξ` satisfies the Killing equation `L_ξ g = 0`. -/
theorem isIntegral_vectorMomentum_of_killing
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieMetric ξ gm μ ν = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) :=
  isIntegral_vectorMomentum_of_lieInverse ((lieInverse_eq_zero_iff hinv ξ).mpr hξ)

/-- `ξ^μ p_μ` is an integral of the motion exactly when `ξ` is a Killing field, `L_ξ g = 0`. -/
theorem isIntegral_vectorMomentum_iff_killing (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (ξ : ι → FreeSmoothRing ι) :
    (canonical ι).IsIntegral (hamiltonian gi) (vectorMomentum ξ) ↔
      ∀ μ ν, lieMetric ξ gm μ ν = 0 :=
  (isIntegral_vectorMomentum_iff (inverse_symm hm hinv) ξ).trans (lieInverse_eq_zero_iff hinv ξ)

/-- The momentum of a co-ordinate on which the metric does not depend is an integral of the
motion. -/
theorem isIntegral_p_of_metric_independent
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {k : ι}
    (h : ∀ μ ν, partialDerivation k (gm μ ν) = 0) :
    (canonical ι).IsIntegral (hamiltonian gi) (p k) := by
  rw [← vectorMomentum_coordinateField k]
  refine isIntegral_vectorMomentum_of_killing hinv fun μ ν => ?_
  rw [lieMetric_coordinateField, h]

/-- The momenta are the lowered velocities: `p_μ = g_{μν} g^{νλ} p_λ`. -/
theorem p_eq_sum_velocity (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0)
    (μ : ι) : p μ = ∑ ν, ofPosition ι (gm μ ν) * velocity gi ν := by
  have h : ∑ ν, ofPosition ι (gm μ ν) * velocity gi ν =
      ∑ l, ofPosition ι (∑ ν, gm μ ν * gi ν l) * p l := by
    simp only [velocity, vectorMomentum, Finset.mul_sum, SmoothRingHom.map_sum, Finset.sum_mul,
      SmoothRingHom.map_mul]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  rw [h]
  simp only [hinv, apply_ite (ofPosition ι), SmoothRingHom.map_one, SmoothRingHom.map_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

omit [DecidableEq ι] in
/-- `H = ½ p_μ ẋ^μ`. -/
theorem hamiltonian_eq_sum :
    hamiltonian gi = algebraMap ℝ (PhaseSpace ι) (1 / 2) * ∑ μ, p μ * velocity gi μ := by
  rw [hamiltonian, quadratic]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [velocity, vectorMomentum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by ring

/-- With the metric, `ṗ_l = {p_l, H} = ½ ∂_l g_{αβ} ẋ^α ẋ^β`. -/
theorem canonical_p_hamiltonian_eq (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (l : ι) :
    (canonical ι).bracket (p l) (hamiltonian gi) =
      algebraMap ℝ (PhaseSpace ι) (1 / 2) *
        ∑ α, ∑ β, ofPosition ι (partialDerivation l (gm α β)) *
          (velocity gi α * velocity gi β) := by
  set D := partialDerivation (Sum.inl l) (ι := ι ⊕ ι)
  have hDp (μ : ι) : D (p μ) = 0 :=
    partialDerivation_generator_of_ne (c := Sum.inl l) (i := Sum.inr μ) (by simp)
  have hDx (f : FreeSmoothRing ι) : D (ofPosition ι f) = ofPosition ι (partialDerivation l f) :=
    partialDerivation_inl_ofPosition l f
  have hD (μ : ι) : ∑ ν, ofPosition ι (gm μ ν) * D (velocity gi ν) =
      -∑ ν, ofPosition ι (partialDerivation l (gm μ ν)) * velocity gi ν := by
    have h := congrArg D (p_eq_sum_velocity hinv μ)
    rw [hDp, map_sum] at h
    simp only [SmoothDerivation.map_mul, smul_eq_mul, hDx, Finset.sum_add_distrib] at h
    have hc : ∑ ν, velocity gi ν * ofPosition ι (partialDerivation l (gm μ ν)) =
        ∑ ν, ofPosition ι (partialDerivation l (gm μ ν)) * velocity gi ν :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hc] at h
    linear_combination -h
  have hsum : ∑ μ, p μ * D (velocity gi μ) =
      -∑ α, ∑ β, ofPosition ι (partialDerivation l (gm α β)) *
        (velocity gi α * velocity gi β) := by
    calc ∑ μ, p μ * D (velocity gi μ)
        = ∑ μ, ∑ ν, ofPosition ι (gm μ ν) * velocity gi ν * D (velocity gi μ) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [p_eq_sum_velocity hinv μ, Finset.sum_mul]
      _ = ∑ ν, velocity gi ν * ∑ μ, ofPosition ι (gm ν μ) * D (velocity gi μ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by rw [hm μ ν]; ring
      _ = _ := by
          simp only [hD, Finset.mul_sum, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [canonical_p_bracket]
  change -(D (hamiltonian gi)) = _
  rw [hamiltonian_eq_sum, SmoothDerivation.map_algebraMap_mul, map_sum]
  simp only [SmoothDerivation.map_mul, smul_eq_mul, hDp, mul_zero, add_zero, hsum]
  ring

/-- The Christoffel symbols of the first kind
`Γ_{μαβ} = ½ (∂_α g_{μβ} + ∂_β g_{μα} − ∂_μ g_{αβ})`. -/
def christoffelLower (gm : ι → ι → FreeSmoothRing ι) (μ α β : ι) : FreeSmoothRing ι :=
  algebraMap ℝ (FreeSmoothRing ι) (1 / 2) *
    (partialDerivation α (gm μ β) + partialDerivation β (gm μ α) - partialDerivation μ (gm α β))

/-- The symmetric part of `∂_α g_{lβ} − Γ_{lαβ}` is `½ ∂_l g_{αβ}`. -/
theorem sum_sub_christoffelLower {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B]
    (φ : SmoothRingHom (FreeSmoothRing ι) B) (v : ι → B) (l : ι) :
    ∑ α, ∑ β, φ (partialDerivation α (gm l β) - christoffelLower gm l α β) * (v α * v β) =
      algebraMap ℝ B (1 / 2) *
        ∑ α, ∑ β, φ (partialDerivation l (gm α β)) * (v α * v β) := by
  have hswap : ∑ α, ∑ β, φ (partialDerivation β (gm l α)) * (v α * v β) =
      ∑ α, ∑ β, φ (partialDerivation α (gm l β)) * (v α * v β) := by
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have hterm (α β : ι) :
      φ (partialDerivation α (gm l β) - christoffelLower gm l α β) * (v α * v β) =
        algebraMap ℝ B (1 / 2) * (φ (partialDerivation α (gm l β)) * (v α * v β)) -
          algebraMap ℝ B (1 / 2) * (φ (partialDerivation β (gm l α)) * (v α * v β)) +
          algebraMap ℝ B (1 / 2) * (φ (partialDerivation l (gm α β)) * (v α * v β)) := by
    rw [christoffelLower, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, SmoothRingHom.map_sub, SmoothRingHom.map_add]
    have h2 := algebraMap_half_mul_two (A := B)
    linear_combination (-(φ (partialDerivation α (gm l β)) * (v α * v β))) * h2
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hswap]
  ring

/-- With the metric, `{p_l, H} = (∂_α g_{lβ} − Γ_{lαβ}) ẋ^α ẋ^β`. -/
theorem canonical_p_hamiltonian_christoffel (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (l : ι) :
    (canonical ι).bracket (p l) (hamiltonian gi) =
      ∑ α, ∑ β, ofPosition ι (partialDerivation α (gm l β) - christoffelLower gm l α β) *
        (velocity gi α * velocity gi β) := by
  rw [sum_sub_christoffelLower, canonical_p_hamiltonian_eq hm hinv]

/-! ### Trajectories and geodesics -/

/-- The positions `x^μ(t)` of a curve of the phase space. -/
def position (c : ι ⊕ ι → TimeFunction) (μ : ι) : TimeFunction := c (Sum.inl μ)

/-- The geodesic equation `g_{μν} ẍ^ν + Γ_{μαβ} ẋ^α ẋ^β = 0` of the chart, for the curve
`x` of the co-ordinates. -/
def IsCoordinateGeodesic (gm : ι → ι → FreeSmoothRing ι) (x : ι → TimeFunction) : Prop :=
  ∀ μ, ∑ ν, lift x (gm μ ν) * timeDerivative (timeDerivative (x ν)) +
    ∑ α, ∑ β, lift x (christoffelLower gm μ α β) *
      (timeDerivative (x α) * timeDerivative (x β)) = 0

/-- The derivative of `f_ν(x) w^ν` along a curve. -/
theorem timeDerivative_sum (x : ι → TimeFunction) (f : ι → FreeSmoothRing ι)
    (w : ι → TimeFunction) :
    timeDerivative (∑ ν, lift x (f ν) * w ν) =
      ∑ ν, lift x (f ν) * timeDerivative (w ν) +
        ∑ α, ∑ β, lift x (partialDerivation α (f β)) * (timeDerivative (x α) * w β) := by
  rw [map_sum]
  simp only [SmoothDerivation.map_mul, smul_eq_mul, derivation_lift_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

omit [DecidableEq ι] in
theorem lift_velocity (c : ι ⊕ ι → TimeFunction) (μ : ι) :
    lift c (velocity gi μ) = ∑ ν, lift (position c) (gi μ ν) * c (Sum.inr ν) := by
  simp only [velocity, vectorMomentum, SmoothRingHom.map_sum, SmoothRingHom.map_mul,
    lift_ofPosition, p, lift_generator]
  rfl

/-- A curve is a trajectory of `H` exactly when `ẋ^μ = g^{μν} p_ν` and
`ṗ_l = (∂_α g_{lβ} − Γ_{lαβ}) ẋ^α ẋ^β`. -/
theorem isTrajectory_iff_velocity (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian gi) c ↔
      (∀ μ, timeDerivative (position c μ) = lift c (velocity gi μ)) ∧
        ∀ l, timeDerivative (c (Sum.inr l)) =
          ∑ α, ∑ β, lift (position c) (partialDerivation α (gm l β) -
            christoffelLower gm l α β) * (lift c (velocity gi α) * lift c (velocity gi β)) := by
  have hs := inverse_symm hm hinv
  unfold IsTrajectory
  rw [Sum.forall]
  have hq (μ : ι) : (generator (Sum.inl μ) : PhaseSpace ι) = q μ := rfl
  have hp (l : ι) : (generator (Sum.inr l) : PhaseSpace ι) = p l := rfl
  simp only [hq, hp, canonical_q_hamiltonian hs, canonical_p_hamiltonian_christoffel hm hinv,
    SmoothRingHom.map_sum, SmoothRingHom.map_mul, lift_ofPosition]
  rfl

/-- **Trajectories are geodesics.** A curve of the phase space is a trajectory of
`H = ½ g^{μν} p_μ p_ν` exactly when its momenta are the lowered velocities `p_μ = g_{μν} ẋ^ν`
and its positions satisfy the geodesic equation of the chart. -/
theorem isTrajectory_iff (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian gi) c ↔
      (∀ μ, c (Sum.inr μ) =
        ∑ ν, lift (position c) (gm μ ν) * timeDerivative (position c ν)) ∧
        IsCoordinateGeodesic gm (position c) := by
  have hP (μ : ι) :
      c (Sum.inr μ) = ∑ ν, lift (position c) (gm μ ν) * lift c (velocity gi ν) := by
    have h := congrArg (lift c) (p_eq_sum_velocity hinv μ)
    simp only [SmoothRingHom.map_sum, SmoothRingHom.map_mul, lift_ofPosition, p,
      lift_generator] at h
    exact h
  have hsplit (l : ι) (w : ι → TimeFunction) :
      ∑ α, ∑ β, lift (position c) (partialDerivation α (gm l β) -
        christoffelLower gm l α β) * (w α * w β) =
      ∑ α, ∑ β, lift (position c) (partialDerivation α (gm l β)) * (w α * w β) -
        ∑ α, ∑ β, lift (position c) (christoffelLower gm l α β) * (w α * w β) := by
    simp only [SmoothRingHom.map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [isTrajectory_iff_velocity hm hinv]
  constructor
  · rintro ⟨hv, hpdot⟩
    have hv' (μ : ι) : lift c (velocity gi μ) = timeDerivative (position c μ) := (hv μ).symm
    have hP' (μ : ι) : c (Sum.inr μ) =
        ∑ ν, lift (position c) (gm μ ν) * timeDerivative (position c ν) := by
      rw [hP μ]
      simp only [hv']
    refine ⟨hP', fun l => ?_⟩
    have h1 := hpdot l
    rw [hP' l, timeDerivative_sum, hsplit] at h1
    simp only [hv'] at h1
    linear_combination h1
  · rintro ⟨hP', hgeo⟩
    have hv (μ : ι) : timeDerivative (position c μ) = lift c (velocity gi μ) := by
      rw [lift_velocity]
      simp only [hP', Finset.mul_sum]
      have h : ∑ l, ∑ ν, lift (position c) (gi μ l) *
          (lift (position c) (gm l ν) * timeDerivative (position c ν)) =
          ∑ ν, lift (position c) (∑ l, gi μ l * gm l ν) * timeDerivative (position c ν) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [SmoothRingHom.map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by rw [SmoothRingHom.map_mul]; ring
      rw [h]
      simp only [inverse_mul hinv, apply_ite (lift (position c)), SmoothRingHom.map_one,
        SmoothRingHom.map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte]
    refine ⟨hv, fun l => ?_⟩
    simp only [← hv]
    rw [hP' l, timeDerivative_sum, hsplit]
    linear_combination hgeo l

/-- The curve that rests at the point `x₀` with zero momenta is a trajectory of `H`, for every
inverse metric: a proved instance of the trajectory hypothesis. -/
theorem isTrajectory_rest (gi : ι → ι → FreeSmoothRing ι) (x₀ : ι → ℝ) :
    IsTrajectory (canonical ι) (hamiltonian gi)
      (Sum.elim (fun μ => algebraMap ℝ TimeFunction (x₀ μ)) fun _ => 0) := by
  have h0 (f : PhaseSpace ι) (hf : f ∈ Ideal.span (Set.range p)) :
      lift (Sum.elim (fun μ => algebraMap ℝ TimeFunction (x₀ μ)) fun _ => 0) f = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨l, rfl⟩
      rw [p, lift_generator, Sum.elim_inr]
    · exact SmoothRingHom.map_zero _
    · intro x y _ _ hx hy
      rw [SmoothRingHom.map_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [smul_eq_mul, SmoothRingHom.map_mul, hx, mul_zero]
  have hp (l : ι) : p l ∈ Ideal.span (Set.range (p (ι := ι))) := Ideal.subset_span ⟨l, rfl⟩
  intro a
  rcases a with μ | l
  · rw [Sum.elim_inl, SmoothDerivation.map_algebraMap]
    refine (h0 _ ?_).symm
    change (canonical ι).bracket (q μ) (hamiltonian gi) ∈ _
    rw [hamiltonian, AlmostPoissonStructure.bracket_mul_right,
      AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero,
      canonical_q_quadratic, vectorMomentum, vectorMomentum]
    exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
      (sum_mem fun ν _ => Ideal.mul_mem_left _ _ (hp ν))
      (sum_mem fun ν _ => Ideal.mul_mem_left _ _ (hp ν)))
  · rw [Sum.elim_inr, map_zero]
    refine (h0 _ ?_).symm
    change (canonical ι).bracket (p l) (hamiltonian gi) ∈ _
    rw [canonical_p_hamiltonian, quadratic]
    exact neg_mem (Ideal.mul_mem_left _ _ (sum_mem fun μ _ =>
      sum_mem fun ν _ => Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hp μ))))

/-- For constant coefficients `G`, the straight line `x(τ) = x₀ + τ G p₀` with the constant
momentum `p₀` is a trajectory: a proved instance with a nonzero velocity, null or timelike as
`G p₀ · p₀` is. -/
theorem isTrajectory_line (G : ι → ι → ℝ) (hG : ∀ μ ν, G μ ν = G ν μ) (x₀ p₀ : ι → ℝ) :
    IsTrajectory (canonical ι) (hamiltonian fun μ ν => algebraMap ℝ (FreeSmoothRing ι) (G μ ν))
      (Sum.elim
        (fun μ => algebraMap ℝ TimeFunction (x₀ μ) +
          algebraMap ℝ TimeFunction (∑ ν, G μ ν * p₀ ν) * SmoothOperation.proj 0)
        fun μ => algebraMap ℝ TimeFunction (p₀ μ)) := by
  set c : ι ⊕ ι → TimeFunction := Sum.elim
    (fun μ => algebraMap ℝ TimeFunction (x₀ μ) +
      algebraMap ℝ TimeFunction (∑ ν, G μ ν * p₀ ν) * SmoothOperation.proj 0)
    fun μ => algebraMap ℝ TimeFunction (p₀ μ)
  have hpos (r : ℝ) : lift c (ofPosition ι (algebraMap ℝ (FreeSmoothRing ι) r)) =
      algebraMap ℝ TimeFunction r := by
    rw [SmoothRingHom.map_algebraMap, SmoothRingHom.map_algebraMap]
  have hpc (ν : ι) : lift c (p ν) = algebraMap ℝ TimeFunction (p₀ ν) := by
    rw [p, lift_generator]
    rfl
  have hs : ∀ μ ν, (fun μ ν => algebraMap ℝ (FreeSmoothRing ι) (G μ ν)) μ ν =
      (fun μ ν => algebraMap ℝ (FreeSmoothRing ι) (G μ ν)) ν μ := fun μ ν => by
    simp only [hG μ ν]
  intro a
  rcases a with μ | l
  · change timeDerivative (c (Sum.inl μ)) =
      lift c ((canonical ι).bracket (q μ) (hamiltonian _))
    rw [canonical_q_hamiltonian hs, velocity, vectorMomentum, SmoothRingHom.map_sum]
    simp only [SmoothRingHom.map_mul, hpos, hpc, ← map_mul, ← map_sum]
    change timeDerivative (algebraMap ℝ TimeFunction (x₀ μ) +
      algebraMap ℝ TimeFunction (∑ ν, G μ ν * p₀ ν) * SmoothOperation.proj 0) = _
    rw [map_add, SmoothDerivation.map_algebraMap, zero_add,
      SmoothDerivation.map_algebraMap_mul, timeDerivative,
      SmoothDerivation.partialDerivation_proj]
    simp only [↓reduceIte, smul_eq_mul, mul_one]
  · change timeDerivative (algebraMap ℝ TimeFunction (p₀ l)) =
      lift c ((canonical ι).bracket (p l) (hamiltonian _))
    rw [SmoothDerivation.map_algebraMap, canonical_p_hamiltonian]
    simp only [SmoothDerivation.map_algebraMap, quadratic, SmoothRingHom.map_zero, zero_mul,
      Finset.sum_const_zero, mul_zero, neg_zero]

/-! ### Killing fields and the red shift -/

/-- The pairing `g(ξ, ẋ) = g_{μν}(x) ξ^μ(x) ẋ^ν` of a vector field with the velocity of a
curve. -/
def pairing (gm : ι → ι → FreeSmoothRing ι) (ξ : ι → FreeSmoothRing ι) (x : ι → TimeFunction) :
    TimeFunction :=
  ∑ μ, ∑ ν, lift x (gm μ ν * ξ μ) * timeDerivative (x ν)

/-- Along a trajectory, `g(ξ, ẋ) = ξ^μ p_μ`. -/
theorem pairing_eq_lift (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian gi) c) (ξ : ι → FreeSmoothRing ι) :
    pairing gm ξ (position c) = lift c (vectorMomentum ξ) := by
  have hP := ((isTrajectory_iff hm hinv c).mp h).1
  simp only [vectorMomentum, SmoothRingHom.map_sum, SmoothRingHom.map_mul, lift_ofPosition, p,
    lift_generator]
  change _ = ∑ μ, lift (position c) (ξ μ) * c (Sum.inr μ)
  simp only [hP, pairing, Finset.mul_sum, SmoothRingHom.map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Conservation of the Killing pairing.** If `ξ` satisfies the Killing equation `L_ξ g = 0`,
then `g(ξ, ẋ)` takes the same value at all times along a trajectory. -/
theorem pairing_eq_of_killing (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian gi) c) {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieMetric ξ gm μ ν = 0) (s t : Fin 1 → ℝ) :
    pairing gm ξ (position c) s = pairing gm ξ (position c) t := by
  rw [pairing_eq_lift hm hinv h]
  exact h.lift_eq_of_isIntegral (isIntegral_vectorMomentum_of_killing hinv hξ) s t

/-- The value `g(ξ, ξ)` of a vector field at the position of a curve. -/
def norm2 (gm : ι → ι → FreeSmoothRing ι) (ξ : ι → FreeSmoothRing ι) (x : ι → TimeFunction) :
    TimeFunction :=
  lift x (∑ μ, ∑ ν, gm μ ν * ξ μ * ξ ν)

/-- The norm `N = √(−g(ξ, ξ))` of a timelike vector field at the position of a curve: the rate of
the proper time of an observer who moves along `ξ` with respect to the parameter of `ξ`, and the
factor of the red shift. -/
def killingNorm (gm : ι → ι → FreeSmoothRing ι) (ξ : ι → FreeSmoothRing ι) (x : ι → TimeFunction)
    (t : Fin 1 → ℝ) : ℝ :=
  Real.sqrt (-norm2 gm ξ x t)

/-- The frequency `ω = −g(ξ/N, ẋ)` of the ray `x` measured by the observer who moves along `ξ`
with the velocity `ξ/N`. -/
def frequency (gm : ι → ι → FreeSmoothRing ι) (ξ : ι → FreeSmoothRing ι) (x : ι → TimeFunction)
    (t : Fin 1 → ℝ) : ℝ :=
  -pairing gm ξ x t / killingNorm gm ξ x t

/-- For a co-ordinate field, `g(∂_k, ∂_k) = g_{kk}`. -/
theorem norm2_coordinateField (k : ι) (x : ι → TimeFunction) :
    norm2 gm (coordinateField k) x = lift x (gm k k) := by
  simp only [norm2, coordinateField, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- For a co-ordinate field, `g(∂_k, ẋ) = g_{kν} ẋ^ν`. -/
theorem pairing_coordinateField (k : ι) (x : ι → TimeFunction) :
    pairing gm (coordinateField k) x = ∑ ν, lift x (gm k ν) * timeDerivative (x ν) := by
  simp only [pairing, coordinateField, mul_ite, mul_one, mul_zero, apply_ite (lift x),
    SmoothRingHom.map_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit [DecidableEq ι] in
theorem killingNorm_mul_frequency {x : ι → TimeFunction} {ξ : ι → FreeSmoothRing ι} {t : Fin 1 → ℝ}
    (ht : norm2 gm ξ x t < 0) :
    killingNorm gm ξ x t * frequency gm ξ x t = -pairing gm ξ x t := by
  have hN : killingNorm gm ξ x t ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr ht)).ne'
  rw [frequency, mul_div_cancel₀ _ hN]

/-- **The red shift.** Let `ξ` be a Killing field, `L_ξ g = 0`, that is timelike at two events
`x(s)` and `x(t)` of a trajectory. The frequencies that the observers along `ξ` measure at these
events satisfy `N(x(s)) ω(s) = N(x(t)) ω(t)`. The trajectory need not be null. -/
theorem killingNorm_mul_frequency_eq (hm : ∀ μ ν, gm μ ν = gm ν μ)
    (hinv : ∀ μ ν, ∑ l, gm μ l * gi l ν = if μ = ν then 1 else 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian gi) c) {ξ : ι → FreeSmoothRing ι}
    (hξ : ∀ μ ν, lieMetric ξ gm μ ν = 0) {s t : Fin 1 → ℝ}
    (hs : norm2 gm ξ (position c) s < 0) (ht : norm2 gm ξ (position c) t < 0) :
    killingNorm gm ξ (position c) s * frequency gm ξ (position c) s =
      killingNorm gm ξ (position c) t * frequency gm ξ (position c) t := by
  rw [killingNorm_mul_frequency hs, killingNorm_mul_frequency ht,
    pairing_eq_of_killing hm hinv h hξ s t]

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian

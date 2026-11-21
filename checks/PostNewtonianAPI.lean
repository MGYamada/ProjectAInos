/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.PostNewtonian

/-! Public consumers of the equations of motion in the second approximation (Landau–Lifshitz
§106): the post-Newtonian metric family with its compatibility and bounds, the lowered geodesic
equation, the explicit post-Newtonian acceleration and its agreement with the geodesics to
`O(c⁻⁴)`, the test-body Lagrangian with its Euler–Lagrange equations, and the instance. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section PostNewtonian

open ContinuousLinearMap Set TopologicalSpace Metric Filter

open scoped ContDiff Topology Matrix Manifold

namespace ProjectAinos.GeneralRelativity.PostNewtonian

open NewtonianMetricFamily

local notation "E" => NewtonianCoordinates

local notation "S" => NewtonianSpace

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {K L a : ℝ} {f g : E → F}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hbf : CoordinateC2Bound U K f)
    (hbg : CoordinateC2Bound U L g) (ha : |a| ≤ 1) :
    CoordinateC2Bound U (K + L) (fun q => f q + a • g q) :=
  coordinateC2Bound_add_smul hf hg hbf hbg ha

namespace Example

example (q : E) :
    ℝ :=
  potential q

example (q : E) :
    ℝ :=
  scalarPotential q

example (q : E) :
    S :=
  vectorPotential q

example (q : E) :
    ℝ :=
  timeRemainder q

example (q : E) :
    S :=
  mixedRemainder q

example (q : E) :
    NewtonianSpatialMatrix :=
  spatialRemainder q

example (q : E) :
    ℝ :=
  timeLeading q

example (q : E) :
    NewtonianSpatialMatrix :=
  spatialLeading q

example :
    ∃ f : PostNewtonianMetricFamily NewtonianExamples.domain,
    f.potential = potential ∧ f.scalarPotential = scalarPotential ∧
      f.vectorPotential = vectorPotential ∧
      f.timeRemainder = (fun _ => timeRemainder) ∧
      f.mixedRemainder = (fun _ => mixedRemainder) ∧
      f.spatialRemainder = (fun _ => spatialRemainder) :=
  exists_family

example :
    PostNewtonianMetricFamily NewtonianExamples.domain :=
  family

example :
    family.potential = potential :=
  family_potential

example :
    family.scalarPotential = scalarPotential :=
  family_scalarPotential

example :
    family.vectorPotential = vectorPotential :=
  family_vectorPotential

example :
    family.timeRemainder = (fun _ => timeRemainder) :=
  family_timeRemainder

example :
    family.mixedRemainder = (fun _ => mixedRemainder) :=
  family_mixedRemainder

example :
    family.spatialRemainder = (fun _ => spatialRemainder) :=
  family_spatialRemainder

end Example

example (D : Fin 4 → Fin 4 → Fin 4 → ℝ) (u : E) (l : Fin 4) :
    ℝ :=
  lowerContraction D u l

example {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  metricDerivative f c q

example {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q u : E) (l : Fin 4) :
    ∑ i, ∑ j, f.lowerChristoffel c q l i j * u i * u j =
      lowerContraction (metricDerivative f c q) u l :=
  sum_lowerChristoffel f c q u l

example {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E) (v : S) :
    ℝ :=
  timeContraction f c q v

example {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ} (hc : 1 ≤ c)
    (hlarge : 9 * f.bound < c ^ 2) (q : U) (v : S) (l : Fin 4) :
    ∑ m : Fin 3, f.coefficient c q l m.succ * f.acceleration c q v m =
      timeContraction f c q v * (∑ n, f.coefficient c q l n * timeVelocity v n) -
        lowerContraction (metricDerivative f c q) (timeVelocity v) l :=
  coefficient_acceleration f hc hlarge q v l

section Partial

variable {g h : E → ℝ} {q : E}

end Partial

example (p : Fin 4 → ℝ) (b : Fin 4 → S) (h : Fin 4 → NewtonianSpatialMatrix) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  blockArray p b h

example (D D' : Fin 4 → Fin 4 → Fin 4 → ℝ) (r : ℝ) (u : E) (l : Fin 4) :
    lowerContraction (fun m a b => D m a b + r * D' m a b) u l =
      lowerContraction D u l + r * lowerContraction D' u l :=
  lowerContraction_add_mul D D' r u l

example (p : Fin 4 → ℝ) (b : Fin 4 → S) (h : Fin 4 → NewtonianSpatialMatrix) (v : S) :
    lowerContraction (blockArray p b h) (timeVelocity v) 0 =
      p 0 / 2 + ∑ j, v j * p j.succ + ∑ i, ∑ j, v i * b i.succ j * v j -
        (∑ i, ∑ j, h 0 i j * v i * v j) / 2 :=
  lowerContraction_block_zero p b h v

example (p : Fin 4 → ℝ) (b : Fin 4 → S) (h : Fin 4 → NewtonianSpatialMatrix) (v : S) (k : Fin 3) :
    lowerContraction (blockArray p b h) (timeVelocity v) k.succ =
      b 0 k + ∑ i, v i * b i.succ k +
        ((∑ j, (h 0 j k + h 0 k j) * v j) +
          ∑ i, v i * ∑ j, (h i.succ j k + h i.succ k j) * v j) / 2 -
        p k.succ / 2 - ∑ j, b k.succ j * v j - (∑ i, ∑ j, h k.succ i j * v i * v j) / 2 :=
  lowerContraction_block_succ p b h v k

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

example (c : ℝ) (q : E) :
    f.coefficient c q 0 0 = -c ^ 2 - 2 * f.potential q + epsilon c *
      (-2 * (f.potential q ^ 2 + f.scalarPotential q) + epsilon c * f.timeRemainder c q) :=
  coefficient_zero_zero f c q

example (c : ℝ) (q : E) (j : Fin 3) :
    f.coefficient c q 0 j.succ =
      epsilon c * (f.vectorPotential q j + epsilon c * f.mixedRemainder c q j) :=
  coefficient_zero_succ f c q j

example (c : ℝ) (q : E) (i : Fin 3) :
    f.coefficient c q i.succ 0 =
      epsilon c * (f.vectorPotential q i + epsilon c * f.mixedRemainder c q i) :=
  coefficient_succ_zero f c q i

example (c : ℝ) (q : E) (i j : Fin 3) :
    f.coefficient c q i.succ j.succ = (if i = j then 1 else 0) + epsilon c *
      (-2 * f.potential q * (if i = j then 1 else 0) + epsilon c * f.spatialRemainder c q i j) :=
  coefficient_succ_succ f c q i j

example (q : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  leadingArray f q

example (q : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  firstArray f q

example (c : ℝ) (q : E) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  secondArray f c q

example {c : ℝ} (hc : 0 < c) {q : E} (hq : q ∈ U) (m a b : Fin 4) :
    metricDerivative f.toNewtonianMetricFamily c q m a b =
      f.leadingArray q m a b + epsilon c * f.firstArray q m a b +
        epsilon c ^ 2 * f.secondArray c q m a b :=
  metricDerivative_eq f hc hq m a b

example {c : ℝ} (hc : 0 < c) {q : E} (hq : q ∈ U) (u : E) (l : Fin 4) :
    lowerContraction (metricDerivative f.toNewtonianMetricFamily c q) u l =
      lowerContraction (f.leadingArray q) u l + epsilon c * lowerContraction (f.firstArray q) u l +
        epsilon c ^ 2 * lowerContraction (f.secondArray c q) u l :=
  lowerContraction_metricDerivative f hc hq u l

example (q : E) (v : S) :
    S :=
  postNewtonianCorrection f q v

example (c : ℝ) (q : E) (v : S) :
    S :=
  postNewtonianAcceleration f c q v

example (q : E) (v : S) (k : Fin 3) :
    f.postNewtonianCorrection q v k =
      -(lowerContraction (f.firstArray q) (timeVelocity v) k.succ +
        2 * f.potential q * coordinatePartial f.potential q k.succ +
        v k * (-coordinatePartial f.potential q 0 -
          2 * ∑ j, v j * coordinatePartial f.potential q j.succ)) :=
  postNewtonianCorrection_eq f q v k

example (ε Φ ψ A ak Φk vk Bk β γ η θ F00 R0 F1k Rk : ℝ) :
    ℝ :=
  coreError ε Φ ψ A ak Φk vk Bk β γ η θ F00 R0 F1k Rk

example (c : ℝ) (q : E) (v : S) (k : Fin 3) :
    ℝ :=
  accelerationRemainder f c q v k

example {c : ℝ} (hc : 1 ≤ c) (hlarge : 9 * f.bound < c ^ 2) (q : U) (v : S) (k : Fin 3) :
    f.acceleration c q v k - f.postNewtonianAcceleration c q v k =
      -(epsilon c ^ 2 * f.accelerationRemainder c q v k) :=
  acceleration_sub_eq f hc hlarge q v k

end PostNewtonianMetricFamily

section BoundedOn

variable {α : Type} {T : Set α} {F G : α → ℝ}

end BoundedOn

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

example {V : ℝ} (hV : 0 ≤ V) :
    ∃ C, 0 ≤ C ∧ ∀ c, 24 * f.bound + 2 ≤ c → ∀ q ∈ U, ∀ v : S, ‖v‖ ≤ V →
      ‖f.acceleration c q v - f.postNewtonianAcceleration c q v‖ ≤ C / c ^ 4 :=
  acceleration_error f hV

example {V : ℝ} (hV : 0 ≤ V) :
    ∃ C, 0 ≤ C ∧ ∀ c (hc : 24 * f.bound + 2 ≤ c), ∀ x q : U, ∀ v : S, ‖v‖ ≤ V →
      ‖coordinateTimeAcceleration (f.lorentzMetric c (by linarith [f.bound_nonneg])
          (by nlinarith [f.bound_nonneg, sq_nonneg (c - 1)])) (physicalChart x) q v -
        f.postNewtonianAcceleration c q v‖ ≤ C / c ^ 4 :=
  native_acceleration_error f hV

example {V : ℝ} (hV : 0 ≤ V) :
    ∃ C, 0 ≤ C ∧ ∀ c (hc : 24 * f.bound + 2 ≤ c) (x : U) {γ : ℝ → U} {r : ℝ → ℝ} {t : ℝ},
      ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) 2 γ (r t) → ContDiffAt ℝ 2 r t → deriv r t ≠ 0 →
      (f.lorentzMetric c (by linarith [f.bound_nonneg])
          (by nlinarith [f.bound_nonneg, sq_nonneg (c - 1)])).covariantAlong
        (SmoothGeometry.LorentzMetric.curveVelocity γ) (r t) = 0 →
      (fun s => physicalChart x (γ (r s)) 0) =ᶠ[𝓝 t] id →
      ‖(fun j : Fin 3 => deriv (physicalChart x ∘ γ ∘ r) t j.succ)‖ ≤ V →
      ‖(fun k : Fin 3 => deriv (deriv (physicalChart x ∘ γ ∘ r)) t k.succ) -
        f.postNewtonianAcceleration c (γ (r t))
          (fun j : Fin 3 => deriv (physicalChart x ∘ γ ∘ r) t j.succ)‖ ≤ C / c ^ 4 :=
  geodesic_acceleration_error f hV

end PostNewtonianMetricFamily

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

example (m c : ℝ) :
    Mechanics.Lagrangian S :=
  lagrangian f m c

example (c : ℝ) (q : E) (v : S) :
    S :=
  lagrangianForce f c q v

example (c : ℝ) (q : E) (v : S) :
    S :=
  lagrangianMomentum f c q v

example (m c t : ℝ) {z : S × S} (hz : (Fin.cons t z.1 : E) ∈ U) (w : S × S) :
    fderiv ℝ (f.lagrangian m c t) z w =
      m * (∑ k, f.lagrangianForce c (Fin.cons t z.1) z.2 k * w.1 k +
        ∑ k, f.lagrangianMomentum c (Fin.cons t z.1) z.2 k * w.2 k) :=
  fderiv_lagrangian f m c t hz w

example (m c : ℝ) (x : ℝ → S) {t : ℝ} (ht : (Fin.cons t (x t) : E) ∈ U) (k : Fin 3) :
    Mechanics.force (f.lagrangian m c) x t (Pi.single k 1) =
      m * f.lagrangianForce c (Fin.cons t (x t)) (deriv x t) k :=
  force_lagrangian f m c x ht k

example (m c : ℝ) (x : ℝ → S) {t : ℝ} (ht : (Fin.cons t (x t) : E) ∈ U) :
    Mechanics.momentum (f.lagrangian m c) x t =
      ∑ k, (m * f.lagrangianMomentum c (Fin.cons t (x t)) (deriv x t) k) • proj k :=
  momentum_lagrangian f m c x ht

example (c : ℝ) (q : E) (v a : S) :
    S :=
  momentumRate f c q v a

example (c : ℝ) {x : ℝ → S} (hx : ContDiff ℝ 2 x) {t : ℝ} (ht : (Fin.cons t (x t) : E) ∈ U)
    (k : Fin 3) :
    HasDerivAt (fun s => f.lagrangianMomentum c (Fin.cons s (x s)) (deriv x s) k)
      (f.momentumRate c (Fin.cons t (x t)) (deriv x t) (deriv (deriv x) t) k) t :=
  hasDerivAt_lagrangianMomentum f c hx ht k

example (m c : ℝ) {x : ℝ → S} (hx : ContDiff ℝ 2 x) {t : ℝ} (ht : (Fin.cons t (x t) : E) ∈ U)
    (k : Fin 3) :
    Mechanics.eulerLagrange (f.lagrangian m c) x t (Pi.single k 1) =
      m * (f.lagrangianForce c (Fin.cons t (x t)) (deriv x t) k -
        f.momentumRate c (Fin.cons t (x t)) (deriv x t) (deriv (deriv x) t) k) :=
  eulerLagrange_lagrangian f m c hx ht k

end PostNewtonianMetricFamily

namespace PostNewtonianMetricFamily

variable {U : Opens E} (f : PostNewtonianMetricFamily U)

example {V : ℝ} (hV : 0 ≤ V) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ m c, m ≠ 0 → c₁ ≤ c → ∀ x : ℝ → S, ContDiff ℝ 2 x → ∀ t,
      (Fin.cons t (x t) : E) ∈ U → ‖deriv x t‖ ≤ V →
      Mechanics.eulerLagrange (f.lagrangian m c) x t = 0 →
      ‖deriv (deriv x) t - f.postNewtonianAcceleration c (Fin.cons t (x t)) (deriv x t)‖ ≤
        C / c ^ 4 :=
  eulerLagrange_acceleration_error f hV

example (m c : ℝ) (hc : 1 ≤ c) (hsmall : 3 * f.bound < c ^ 2) {t : ℝ} {x₀ : S}
    (h₀ : (Fin.cons t x₀ : E) ∈ U) :
    ∃ x : ℝ → S, ContDiff ℝ 2 x ∧ x t = x₀ ∧ deriv x t = 0 ∧
      Mechanics.eulerLagrange (f.lagrangian m c) x t = 0 :=
  exists_eulerLagrange_rest f m c hc hsmall h₀

example {V : ℝ} (hV : 0 ≤ V) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ m c, m ≠ 0 → c₁ ≤ c → ∀ x : ℝ → S, ContDiff ℝ 2 x → ∀ t,
      (Fin.cons t (x t) : E) ∈ U → ‖deriv x t‖ ≤ V →
      Mechanics.eulerLagrange (f.lagrangian m c) x t = 0 →
      ‖deriv (deriv x) t - f.acceleration c (Fin.cons t (x t)) (deriv x t)‖ ≤ C / c ^ 4 :=
  eulerLagrange_sub_acceleration f hV

end PostNewtonianMetricFamily

end ProjectAinos.GeneralRelativity.PostNewtonian

end PostNewtonian

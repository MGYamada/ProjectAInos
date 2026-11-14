/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Constants
public import ProjectAInos.Mechanics.Hyperregular
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Routhian

Landau–Lifshitz §41. The co-ordinates are `q_i` for `i : ι` and `q_k` for
`k : κ`. The partial Legendre transformation of a Lagrangian `L(q, v)` replaces
the velocities `v_k` by the momenta `p_k = ∂L/∂v_k` and keeps the velocities
`v_i`. `L` is hyperregular in the velocities `v_k` when this morphism has an
inverse `G`; the Routhian is then `R = G(Σ_k v_k ∂L/∂v_k − L)`.

* `IsPartiallyHyperregular.partialLegendre_partialDerivation_p_routhian`,
  `IsPartiallyHyperregular.partialLegendre_partialDerivation_q_routhian`,
  `IsPartiallyHyperregular.partialLegendre_partialDerivation_v_routhian`:
  `∂R/∂p_k = v_k`, `∂R/∂q_a = −∂L/∂q_a` and `∂R/∂v_i = −∂L/∂v_i`.
* `IsPartiallyHyperregular.isRouthTrajectory_routhCurve_iff`: the
  Euler–Lagrange equations of `L` are the equations of the Routhian, which are
  Lagrange's equations in the co-ordinates `q_i` and Hamilton's equations in
  the co-ordinates `q_k`.
* `IsRouthTrajectory.isSolution_reducedRouthian`: if the co-ordinates `q_k` are
  cyclic, the momenta `p_k` are constant, and the co-ordinates `q_i` satisfy
  the Euler–Lagrange equations of the Routhian at these values of the momenta.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The ring of functions of the positions `q_a`, the velocities `v_i` and the
momenta `p_k`. -/
abbrev RouthSpace (ι κ : Type*) := FreeSmoothRing ((ι ⊕ κ) ⊕ (ι ⊕ κ))

namespace RouthSpace

variable {ι κ : Type*}

/-- The position `q_a`. -/
def q (a : ι ⊕ κ) : RouthSpace ι κ := generator (Sum.inl a)

/-- The velocity `v_i` of a co-ordinate that is not transformed. -/
def v (i : ι) : RouthSpace ι κ := generator (Sum.inr (Sum.inl i))

/-- The momentum `p_k` of a transformed co-ordinate. -/
def p (k : κ) : RouthSpace ι κ := generator (Sum.inr (Sum.inr k))

end RouthSpace

namespace Routhian

open VelocitySpace

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The partial Legendre transformation: `q_a ↦ q_a`, `v_i ↦ v_i` and
`p_k ↦ ∂L/∂v_k`. -/
def partialLegendre (L : VelocitySpace (ι ⊕ κ)) :
    SmoothRingHom (RouthSpace ι κ) (VelocitySpace (ι ⊕ κ)) :=
  FreeSmoothRing.lift (Sum.elim VelocitySpace.q
    (Sum.elim (fun i => VelocitySpace.v (Sum.inl i)) fun k => momentum L (Sum.inr k)))

theorem partialLegendre_q (L : VelocitySpace (ι ⊕ κ)) (a : ι ⊕ κ) :
    partialLegendre L (RouthSpace.q a) = VelocitySpace.q a := lift_generator _ _

theorem partialLegendre_v (L : VelocitySpace (ι ⊕ κ)) (i : ι) :
    partialLegendre L (RouthSpace.v i) = VelocitySpace.v (Sum.inl i) := lift_generator _ _

theorem partialLegendre_p (L : VelocitySpace (ι ⊕ κ)) (k : κ) :
    partialLegendre L (RouthSpace.p k) = momentum L (Sum.inr k) := lift_generator _ _

variable [Fintype ι] [Fintype κ]

/-- The energy of the transformed co-ordinates, `Σ_k v_k ∂L/∂v_k − L`. -/
def partialEnergy (L : VelocitySpace (ι ⊕ κ)) : VelocitySpace (ι ⊕ κ) :=
  ∑ k : κ, VelocitySpace.v (Sum.inr k) * momentum L (Sum.inr k) - L

/-- The matrix `∂²L/∂v_k∂v_l` of the transformed velocities. -/
def partialHessian (L : VelocitySpace (ι ⊕ κ)) : Matrix κ κ (VelocitySpace (ι ⊕ κ)) :=
  Matrix.of fun k l => partialDerivation (Sum.inr (Sum.inr l)) (momentum L (Sum.inr k))

/-- The chain rule for the partial Legendre transformation. -/
theorem apply_partialLegendre (L : VelocitySpace (ι ⊕ κ))
    (E : SmoothDerivation (VelocitySpace (ι ⊕ κ)) (VelocitySpace (ι ⊕ κ)))
    (s : RouthSpace ι κ) :
    E (partialLegendre L s) =
      ∑ a, partialLegendre L (partialDerivation (Sum.inl a) s) * E (VelocitySpace.q a) +
        (∑ i, partialLegendre L (partialDerivation (Sum.inr (Sum.inl i)) s) *
            E (VelocitySpace.v (Sum.inl i)) +
          ∑ k, partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) s) *
            E (momentum L (Sum.inr k))) := by
  rw [partialLegendre, derivation_lift_mul, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_sum_type]
  rfl

/-- The derivative of a transformed function in a transformed velocity. -/
theorem partialDerivation_p_partialLegendre (L : VelocitySpace (ι ⊕ κ)) (s : RouthSpace ι κ)
    (l : κ) :
    partialDerivation (Sum.inr (Sum.inr l)) (partialLegendre L s) =
      ∑ k, partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) s) *
        partialHessian L k l := by
  rw [apply_partialLegendre, Finset.sum_eq_zero, zero_add, Finset.sum_eq_zero, zero_add]
  · rfl
  · intro i _
    rw [VelocitySpace.v, partialDerivation_generator_of_ne (by simp), mul_zero]
  · intro a _
    rw [VelocitySpace.q, partialDerivation_generator_of_ne (by simp), mul_zero]

/-- The derivative of a transformed function in a position. -/
theorem partialDerivation_q_partialLegendre (L : VelocitySpace (ι ⊕ κ)) (s : RouthSpace ι κ)
    (b : ι ⊕ κ) :
    partialDerivation (Sum.inl b) (partialLegendre L s) =
      partialLegendre L (partialDerivation (Sum.inl b) s) +
        ∑ k, partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) s) *
          partialDerivation (Sum.inl b) (momentum L (Sum.inr k)) := by
  rw [apply_partialLegendre, Finset.sum_eq_single b, Finset.sum_eq_zero, zero_add]
  · rw [VelocitySpace.q, partialDerivation_generator_self, mul_one]
  · intro i _
    rw [VelocitySpace.v, partialDerivation_generator_of_ne (by simp), mul_zero]
  · intro a _ ha
    rw [VelocitySpace.q, partialDerivation_generator_of_ne (fun h => ha (Sum.inl.inj h)),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- The derivative of a transformed function in a velocity that is not
transformed. -/
theorem partialDerivation_v_partialLegendre (L : VelocitySpace (ι ⊕ κ)) (s : RouthSpace ι κ)
    (j : ι) :
    partialDerivation (Sum.inr (Sum.inl j)) (partialLegendre L s) =
      partialLegendre L (partialDerivation (Sum.inr (Sum.inl j)) s) +
        ∑ k, partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) s) *
          partialDerivation (Sum.inr (Sum.inl j)) (momentum L (Sum.inr k)) := by
  rw [apply_partialLegendre, Finset.sum_eq_zero, zero_add, Finset.sum_eq_single j]
  · rw [VelocitySpace.v, partialDerivation_generator_self, mul_one]
  · intro i _ hi
    rw [VelocitySpace.v,
      partialDerivation_generator_of_ne (fun h => hi (Sum.inl.inj (Sum.inr.inj h))), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h
  · intro a _
    rw [VelocitySpace.q, partialDerivation_generator_of_ne (by simp), mul_zero]

omit [Fintype ι] in
/-- `∂E/∂v_l = Σ_k v_k ∂²L/∂v_k∂v_l` for the energy of the transformed
co-ordinates. -/
theorem partialDerivation_p_partialEnergy (L : VelocitySpace (ι ⊕ κ)) (l : κ) :
    partialDerivation (Sum.inr (Sum.inr l)) (partialEnergy L) =
      ∑ k, VelocitySpace.v (Sum.inr k) * partialHessian L k l := by
  have h (k : κ) : partialDerivation (Sum.inr (Sum.inr l))
      (VelocitySpace.v (Sum.inr k) * momentum L (Sum.inr k)) =
      VelocitySpace.v (Sum.inr k) * partialHessian L k l +
        if k = l then momentum L (Sum.inr k) else 0 := by
    rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul, VelocitySpace.v,
      partialDerivation_generator]
    simp only [Sum.inr.injEq, mul_ite, mul_one, mul_zero]
    rfl
  rw [partialEnergy, map_sub, map_sum]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact add_sub_cancel_right _ _

omit [Fintype ι] in
/-- The derivative of the energy of the transformed co-ordinates in a
co-ordinate that is not a transformed velocity. -/
theorem partialDerivation_partialEnergy_of_ne (L : VelocitySpace (ι ⊕ κ))
    {x : (ι ⊕ κ) ⊕ (ι ⊕ κ)} (hx : ∀ k : κ, Sum.inr (Sum.inr k) ≠ x) :
    partialDerivation x (partialEnergy L) =
      ∑ k, VelocitySpace.v (Sum.inr k) * partialDerivation x (momentum L (Sum.inr k)) -
        partialDerivation x L := by
  rw [partialEnergy, map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul, VelocitySpace.v,
    partialDerivation_generator_of_ne (hx k), mul_zero, add_zero]

/-- `L` is hyperregular in the velocities `v_k`, with the inverse `G` of its
partial Legendre transformation. -/
structure IsPartiallyHyperregular (L : VelocitySpace (ι ⊕ κ))
    (G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)) : Prop where
  left_inv : G.comp (partialLegendre L) = SmoothRingHom.id (RouthSpace ι κ)
  right_inv : (partialLegendre L).comp G = SmoothRingHom.id (VelocitySpace (ι ⊕ κ))

/-- The Routhian `R = G(Σ_k v_k ∂L/∂v_k − L)`. -/
def routhian (L : VelocitySpace (ι ⊕ κ))
    (G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)) : RouthSpace ι κ :=
  G (partialEnergy L)

/-- The inverse of the matrix `∂²L/∂v_k∂v_l` of the transformed velocities. -/
def inversePartialHessian (L : VelocitySpace (ι ⊕ κ))
    (G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)) :
    Matrix κ κ (VelocitySpace (ι ⊕ κ)) :=
  Matrix.of fun k l =>
    partialLegendre L (partialDerivation (Sum.inr (Sum.inr l)) (G (VelocitySpace.v (Sum.inr k))))

namespace IsPartiallyHyperregular

variable {L : VelocitySpace (ι ⊕ κ)} {G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)}

omit [Fintype ι] [Fintype κ] in
theorem apply_partialLegendre (h : IsPartiallyHyperregular L G) (s : RouthSpace ι κ) :
    G (partialLegendre L s) = s :=
  congrArg (fun φ : SmoothRingHom (RouthSpace ι κ) (RouthSpace ι κ) => φ s) h.left_inv

omit [Fintype ι] [Fintype κ] in
theorem partialLegendre_apply (h : IsPartiallyHyperregular L G) (x : VelocitySpace (ι ⊕ κ)) :
    partialLegendre L (G x) = x :=
  congrArg (fun φ : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (VelocitySpace (ι ⊕ κ)) => φ x)
    h.right_inv

omit [Fintype ι] in
/-- The partial Legendre transformation takes the Routhian to the energy of
the transformed co-ordinates. -/
theorem partialLegendre_routhian (h : IsPartiallyHyperregular L G) :
    partialLegendre L (routhian L G) = partialEnergy L :=
  h.partialLegendre_apply _

omit [Fintype ι] [Fintype κ] in
theorem apply_q (h : IsPartiallyHyperregular L G) (a : ι ⊕ κ) :
    G (VelocitySpace.q a) = RouthSpace.q a := by
  rw [← partialLegendre_q L, h.apply_partialLegendre]

omit [Fintype ι] [Fintype κ] in
theorem apply_v_inl (h : IsPartiallyHyperregular L G) (i : ι) :
    G (VelocitySpace.v (Sum.inl i)) = RouthSpace.v i := by
  rw [← partialLegendre_v L, h.apply_partialLegendre]

omit [Fintype ι] [Fintype κ] in
theorem apply_momentum (h : IsPartiallyHyperregular L G) (k : κ) :
    G (momentum L (Sum.inr k)) = RouthSpace.p k := by
  rw [← partialLegendre_p L, h.apply_partialLegendre]

/-- The matrix `∂²L/∂v_k∂v_l` of the transformed velocities is invertible. -/
theorem inversePartialHessian_mul_partialHessian (h : IsPartiallyHyperregular L G) :
    inversePartialHessian L G * partialHessian L = 1 := by
  refine Matrix.ext fun k l => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h1 := partialDerivation_p_partialLegendre L (G (VelocitySpace.v (Sum.inr k))) l
  rw [h.partialLegendre_apply, VelocitySpace.v, partialDerivation_generator] at h1
  simp only [Sum.inr.injEq] at h1
  exact h1.symm

theorem partialHessian_mul_inversePartialHessian (h : IsPartiallyHyperregular L G) :
    partialHessian L * inversePartialHessian L G = 1 :=
  mul_eq_one_comm.mp h.inversePartialHessian_mul_partialHessian

theorem eq_zero_of_vecMul_partialHessian (h : IsPartiallyHyperregular L G)
    {x : κ → VelocitySpace (ι ⊕ κ)} (hx : x ᵥ* partialHessian L = 0) : x = 0 := by
  calc x = x ᵥ* (partialHessian L * inversePartialHessian L G) := by
        rw [h.partialHessian_mul_inversePartialHessian, Matrix.vecMul_one]
    _ = (x ᵥ* partialHessian L) ᵥ* inversePartialHessian L G :=
        (Matrix.vecMul_vecMul x _ _).symm
    _ = 0 := by rw [hx, Matrix.zero_vecMul]

/-- `∂R/∂p_k = v_k`, read in the positions and the velocities. -/
theorem partialLegendre_partialDerivation_p_routhian (h : IsPartiallyHyperregular L G)
    (k : κ) :
    partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) (routhian L G)) =
      VelocitySpace.v (Sum.inr k) := by
  have hx : (fun k => partialLegendre L
      (partialDerivation (Sum.inr (Sum.inr k)) (routhian L G)) - VelocitySpace.v (Sum.inr k)) =
      0 :=
    h.eq_zero_of_vecMul_partialHessian (funext fun l => by
      change ∑ k, (partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) (routhian L G)) -
        VelocitySpace.v (Sum.inr k)) * partialHessian L k l = 0
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [← partialDerivation_p_partialLegendre, ← partialDerivation_p_partialEnergy,
        h.partialLegendre_routhian, sub_self])
  exact sub_eq_zero.mp (congrFun hx k)

/-- `∂R/∂q_a = −∂L/∂q_a`, read in the positions and the velocities. -/
theorem partialLegendre_partialDerivation_q_routhian (h : IsPartiallyHyperregular L G)
    (b : ι ⊕ κ) :
    partialLegendre L (partialDerivation (Sum.inl b) (routhian L G)) =
      -partialDerivation (Sum.inl b) L := by
  have h1 := partialDerivation_q_partialLegendre L (routhian L G) b
  rw [h.partialLegendre_routhian, partialDerivation_partialEnergy_of_ne L (by simp)] at h1
  simp only [h.partialLegendre_partialDerivation_p_routhian] at h1
  linear_combination -h1

/-- `∂R/∂v_i = −∂L/∂v_i`, read in the positions and the velocities. -/
theorem partialLegendre_partialDerivation_v_routhian (h : IsPartiallyHyperregular L G)
    (j : ι) :
    partialLegendre L (partialDerivation (Sum.inr (Sum.inl j)) (routhian L G)) =
      -partialDerivation (Sum.inr (Sum.inl j)) L := by
  have h1 := partialDerivation_v_partialLegendre L (routhian L G) j
  rw [h.partialLegendre_routhian, partialDerivation_partialEnergy_of_ne L (by simp)] at h1
  simp only [h.partialLegendre_partialDerivation_p_routhian] at h1
  linear_combination -h1

/-- `G(v_k) = ∂R/∂p_k`. -/
theorem apply_v_inr (h : IsPartiallyHyperregular L G) (k : κ) :
    G (VelocitySpace.v (Sum.inr k)) =
      partialDerivation (Sum.inr (Sum.inr k)) (routhian L G) := by
  rw [← h.partialLegendre_partialDerivation_p_routhian k, h.apply_partialLegendre]

/-- `∂R/∂q_a = −G(∂L/∂q_a)`. -/
theorem partialDerivation_q_routhian (h : IsPartiallyHyperregular L G) (b : ι ⊕ κ) :
    partialDerivation (Sum.inl b) (routhian L G) = -G (partialDerivation (Sum.inl b) L) := by
  rw [← SmoothRingHom.map_neg, ← h.partialLegendre_partialDerivation_q_routhian b,
    h.apply_partialLegendre]

/-- A cyclic co-ordinate of the Lagrangian is a cyclic co-ordinate of the
Routhian. -/
theorem partialDerivation_q_routhian_eq_zero (h : IsPartiallyHyperregular L G) {b : ι ⊕ κ}
    (hL : partialDerivation (Sum.inl b) L = 0) :
    partialDerivation (Sum.inl b) (routhian L G) = 0 := by
  rw [h.partialDerivation_q_routhian, hL, SmoothRingHom.map_zero, neg_zero]

end IsPartiallyHyperregular

/-! ### The equations of motion -/

/-- The curve of the positions, the velocities `v_i` and the momenta
`p_k = ∂L/∂v_k` of a path. -/
def routhCurve (L : VelocitySpace (ι ⊕ κ))
    (γ : ι ⊕ κ → TimeFunction) : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction :=
  Sum.elim γ (Sum.elim (fun i => timeDerivative (γ (Sum.inl i)))
    fun k => FreeSmoothRing.lift (velocityCurve γ) (momentum L (Sum.inr k)))

omit [Fintype ι] [Fintype κ] in
/-- A function of the positions, the velocities `v_i` and the momenta `p_k`
along the curve of a path. -/
theorem lift_routhCurve (L : VelocitySpace (ι ⊕ κ)) (γ : ι ⊕ κ → TimeFunction)
    (s : RouthSpace ι κ) :
    FreeSmoothRing.lift (routhCurve L γ) s =
      FreeSmoothRing.lift (velocityCurve γ) (partialLegendre L s) := by
  rw [partialLegendre, map_lift]
  refine congrArg (fun y => FreeSmoothRing.lift y s) (funext fun a => ?_)
  rcases a with a | i | k
  · change γ a = FreeSmoothRing.lift (velocityCurve γ) (generator (Sum.inl a))
    rw [lift_generator]
    rfl
  · change timeDerivative (γ (Sum.inl i)) =
      FreeSmoothRing.lift (velocityCurve γ) (generator (Sum.inr (Sum.inl i)))
    rw [lift_generator]
    rfl
  · rfl

/-- The equations of motion of a Routhian `R` along a curve: Lagrange's
equations in the co-ordinates `q_i`, with `R` as the Lagrangian, and Hamilton's
equations in the co-ordinates `q_k`, with `R` as the Hamiltonian. -/
structure IsRouthTrajectory (R : RouthSpace ι κ) (c : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction) :
    Prop where
  velocity : ∀ i : ι, timeDerivative (c (Sum.inl (Sum.inl i))) = c (Sum.inr (Sum.inl i))
  lagrange : ∀ i : ι,
    timeDerivative (FreeSmoothRing.lift c (partialDerivation (Sum.inr (Sum.inl i)) R)) =
      FreeSmoothRing.lift c (partialDerivation (Sum.inl (Sum.inl i)) R)
  hamilton_q : ∀ k : κ, timeDerivative (c (Sum.inl (Sum.inr k))) =
    FreeSmoothRing.lift c (partialDerivation (Sum.inr (Sum.inr k)) R)
  hamilton_p : ∀ k : κ, timeDerivative (c (Sum.inr (Sum.inr k))) =
    -FreeSmoothRing.lift c (partialDerivation (Sum.inl (Sum.inr k)) R)

namespace IsPartiallyHyperregular

variable {L : VelocitySpace (ι ⊕ κ)} {G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)}

/-- The Routhian (Landau–Lifshitz §41): a path satisfies the Euler–Lagrange
equations of `L` exactly when its curve of positions, velocities `v_i` and
momenta `p_k` satisfies the equations of the Routhian. -/
theorem isRouthTrajectory_routhCurve_iff (h : IsPartiallyHyperregular L G)
    (γ : ι ⊕ κ → TimeFunction) :
    IsRouthTrajectory (routhian L G) (routhCurve L γ) ↔ StandardJet.IsSolution (toJet L) γ := by
  rw [isSolution_toJet_iff]
  constructor
  · intro hR a
    rcases a with i | k
    · have h2 := hR.lagrange i
      rw [lift_routhCurve, lift_routhCurve, h.partialLegendre_partialDerivation_v_routhian,
        h.partialLegendre_partialDerivation_q_routhian, SmoothRingHom.map_neg,
        SmoothRingHom.map_neg, map_neg] at h2
      exact neg_injective h2
    · have h4 := hR.hamilton_p k
      rw [lift_routhCurve, h.partialLegendre_partialDerivation_q_routhian,
        SmoothRingHom.map_neg, neg_neg] at h4
      exact h4
  · intro hEL
    refine ⟨fun i => rfl, fun i => ?_, fun k => ?_, fun k => ?_⟩
    · rw [lift_routhCurve, lift_routhCurve, h.partialLegendre_partialDerivation_v_routhian,
        h.partialLegendre_partialDerivation_q_routhian, SmoothRingHom.map_neg,
        SmoothRingHom.map_neg, map_neg]
      exact congrArg Neg.neg (hEL (Sum.inl i))
    · rw [lift_routhCurve, h.partialLegendre_partialDerivation_p_routhian, VelocitySpace.v,
        lift_generator]
      rfl
    · rw [lift_routhCurve, h.partialLegendre_partialDerivation_q_routhian,
        SmoothRingHom.map_neg, neg_neg]
      exact hEL (Sum.inr k)

/-- A curve that satisfies the equations of the Routhian is the curve of its
path: its velocities are the derivatives of its positions and its momenta are
`p_k = ∂L/∂v_k`. -/
theorem eq_routhCurve (h : IsPartiallyHyperregular L G) {c : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}
    (hc : IsRouthTrajectory (routhian L G) c) : c = routhCurve L fun a => c (Sum.inl a) := by
  have hG : (FreeSmoothRing.lift c).comp G =
      FreeSmoothRing.lift (velocityCurve fun a => c (Sum.inl a)) :=
    FreeSmoothRing.hom_ext fun a => by
      rw [SmoothRingHom.comp_apply, lift_generator]
      rcases a with a | i | k
      · change FreeSmoothRing.lift c (G (VelocitySpace.q a)) = c (Sum.inl a)
        rw [h.apply_q, RouthSpace.q, lift_generator]
      · change FreeSmoothRing.lift c (G (VelocitySpace.v (Sum.inl i))) =
          timeDerivative (c (Sum.inl (Sum.inl i)))
        rw [h.apply_v_inl, RouthSpace.v, lift_generator, hc.velocity]
      · change FreeSmoothRing.lift c (G (VelocitySpace.v (Sum.inr k))) =
          timeDerivative (c (Sum.inl (Sum.inr k)))
        rw [h.apply_v_inr, hc.hamilton_q]
  funext a
  rcases a with a | i | k
  · rfl
  · exact (hc.velocity i).symm
  · change c (Sum.inr (Sum.inr k)) =
      FreeSmoothRing.lift (velocityCurve fun a => c (Sum.inl a)) (momentum L (Sum.inr k))
    rw [← hG, SmoothRingHom.comp_apply, h.apply_momentum, RouthSpace.p, lift_generator]

end IsPartiallyHyperregular

/-! ### Cyclic co-ordinates -/

variable (ι) in
/-- A function at `q_k = 0`, `p_k = c_k`, as a function of the remaining
positions and velocities. -/
def restriction (c : κ → ℝ) : SmoothRingHom (RouthSpace ι κ) (VelocitySpace ι) :=
  FreeSmoothRing.lift (Sum.elim (Sum.elim VelocitySpace.q fun _ => 0)
    (Sum.elim VelocitySpace.v fun k => algebraMap ℝ (VelocitySpace ι) (c k)))

/-- The Routhian at the values `c_k` of the momenta, as a Lagrangian of the
remaining co-ordinates. -/
def reducedRouthian (R : RouthSpace ι κ) (c : κ → ℝ) : VelocitySpace ι := restriction ι c R

theorem partialDerivation_inl_restriction (c : κ → ℝ) (s : RouthSpace ι κ) (i : ι) :
    partialDerivation (Sum.inl i) (restriction ι c s) =
      restriction ι c (partialDerivation (Sum.inl (Sum.inl i)) s) := by
  rw [restriction, derivation_lift_mul, Finset.sum_eq_single (Sum.inl (Sum.inl i))]
  · rw [Sum.elim_inl, Sum.elim_inl, VelocitySpace.q, partialDerivation_generator_self, mul_one]
  · intro a _ ha
    rcases a with (j | k) | (j | k)
    · rw [Sum.elim_inl, Sum.elim_inl, VelocitySpace.q,
        partialDerivation_generator_of_ne (fun h => ha (by rw [Sum.inl.inj h])), mul_zero]
    · rw [Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero]
    · rw [Sum.elim_inr, Sum.elim_inl, VelocitySpace.v,
        partialDerivation_generator_of_ne (by simp), mul_zero]
    · rw [Sum.elim_inr, Sum.elim_inr, SmoothDerivation.map_algebraMap, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem partialDerivation_inr_restriction (c : κ → ℝ) (s : RouthSpace ι κ) (i : ι) :
    partialDerivation (Sum.inr i) (restriction ι c s) =
      restriction ι c (partialDerivation (Sum.inr (Sum.inl i)) s) := by
  rw [restriction, derivation_lift_mul, Finset.sum_eq_single (Sum.inr (Sum.inl i))]
  · rw [Sum.elim_inr, Sum.elim_inl, VelocitySpace.v, partialDerivation_generator_self, mul_one]
  · intro a _ ha
    rcases a with (j | k) | (j | k)
    · rw [Sum.elim_inl, Sum.elim_inl, VelocitySpace.q,
        partialDerivation_generator_of_ne (by simp), mul_zero]
    · rw [Sum.elim_inl, Sum.elim_inr, map_zero, mul_zero]
    · rw [Sum.elim_inr, Sum.elim_inl, VelocitySpace.v,
        partialDerivation_generator_of_ne (fun h => ha (by rw [Sum.inr.inj h])), mul_zero]
    · rw [Sum.elim_inr, Sum.elim_inr, SmoothDerivation.map_algebraMap, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

namespace IsRouthTrajectory

variable {R : RouthSpace ι κ} {x : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}

omit [Fintype ι] [Fintype κ] in
/-- The momentum of a cyclic co-ordinate is constant along the motion. -/
theorem p_eq_algebraMap (hx : IsRouthTrajectory R x) {k : κ}
    (hR : partialDerivation (Sum.inl (Sum.inr k)) R = 0) :
    x (Sum.inr (Sum.inr k)) = algebraMap ℝ TimeFunction (x (Sum.inr (Sum.inr k)) fun _ => 0) := by
  refine SmoothOperation.ext fun t => ?_
  have h0 : timeDerivative (x (Sum.inr (Sum.inr k))) = 0 := by
    rw [hx.hamilton_p, hR, SmoothRingHom.map_zero, neg_zero]
  rw [TimeFunction.eq_of_timeDerivative_eq_zero h0 t fun _ => 0, TimeFunction.algebraMap_apply]

omit [Fintype ι] [Fintype κ] in
/-- Along a curve with `v_i = q̇_i` and `p_k = c_k`, a function that does not
depend on the cyclic co-ordinates is its restriction along the path of the
remaining co-ordinates. -/
theorem lift_restriction (hx : IsRouthTrajectory R x) {c : κ → ℝ}
    (hc : ∀ k, x (Sum.inr (Sum.inr k)) = algebraMap ℝ TimeFunction (c k)) {s : RouthSpace ι κ}
    (hs : ∀ k, partialDerivation (Sum.inl (Sum.inr k)) s = 0) :
    FreeSmoothRing.lift (velocityCurve fun i => x (Sum.inl (Sum.inl i))) (restriction ι c s) =
      FreeSmoothRing.lift x s := by
  have hdrop : FreeSmoothRing.lift (Sum.elim
      (Sum.elim (fun i => (generator (Sum.inl (Sum.inl i)) : RouthSpace ι κ)) fun _ => 0)
      fun a => generator (Sum.inr a)) s = s :=
    lift_eq_self_of_partialDerivation_eq_zero fun a ha => by
      rcases a with (i | k) | a
      · exact absurd rfl ha
      · exact hs k
      · exact absurd rfl ha
  have hq (i : ι) : FreeSmoothRing.lift (velocityCurve fun i => x (Sum.inl (Sum.inl i)))
      (VelocitySpace.q i) = x (Sum.inl (Sum.inl i)) := by
    rw [VelocitySpace.q, lift_generator]
    rfl
  have hv (i : ι) : FreeSmoothRing.lift (velocityCurve fun i => x (Sum.inl (Sum.inl i)))
      (VelocitySpace.v i) = x (Sum.inr (Sum.inl i)) := by
    rw [VelocitySpace.v, lift_generator]
    exact hx.velocity i
  conv_rhs => rw [← hdrop]
  rw [restriction, map_lift, map_lift]
  refine congrArg (fun y => FreeSmoothRing.lift y s) (funext fun a => ?_)
  rcases a with (i | k) | (i | k)
  · simp only [Sum.elim_inl]
    rw [hq, lift_generator]
  · simp only [Sum.elim_inl, Sum.elim_inr, SmoothRingHom.map_zero]
  · simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hv, lift_generator]
  · simp only [Sum.elim_inr]
    rw [SmoothRingHom.map_algebraMap, lift_generator, hc]

/-- Cyclic co-ordinates (Landau–Lifshitz §41): if the Routhian does not depend
on the co-ordinates `q_k` and the momenta `p_k` have the values `c_k`, the
remaining co-ordinates satisfy the Euler–Lagrange equations of the Routhian at
these values of the momenta. -/
theorem isSolution_reducedRouthian (hx : IsRouthTrajectory R x)
    (hR : ∀ k, partialDerivation (Sum.inl (Sum.inr k)) R = 0) {c : κ → ℝ}
    (hc : ∀ k, x (Sum.inr (Sum.inr k)) = algebraMap ℝ TimeFunction (c k)) :
    StandardJet.IsSolution (toJet (reducedRouthian R c)) fun i => x (Sum.inl (Sum.inl i)) := by
  rw [isSolution_toJet_iff]
  intro i
  have hcomm (a : (ι ⊕ κ) ⊕ (ι ⊕ κ)) (k : κ) :
      partialDerivation (Sum.inl (Sum.inr k)) (partialDerivation a R) = 0 := by
    rw [partialDerivation_comm, hR k, map_zero]
  rw [momentum, reducedRouthian, partialDerivation_inr_restriction,
    partialDerivation_inl_restriction, hx.lift_restriction hc (hcomm _),
    hx.lift_restriction hc (hcomm _)]
  exact hx.lagrange i

end IsRouthTrajectory

/-! ### Natural Lagrangians -/

/-- The inverse of the partial Legendre transformation of a natural
Lagrangian: `q_a ↦ q_a`, `v_i ↦ v_i` and `v_k ↦ p_k / m_k`. -/
def naturalInverse (m : ι ⊕ κ → ℝ) : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ) :=
  FreeSmoothRing.lift (Sum.elim RouthSpace.q (Sum.elim RouthSpace.v
    fun k => algebraMap ℝ (RouthSpace ι κ) (m (Sum.inr k))⁻¹ * RouthSpace.p k))

/-- A natural Lagrangian is hyperregular in the velocities of the co-ordinates
with non-zero masses. -/
theorem isPartiallyHyperregular_natural {m : ι ⊕ κ → ℝ} (hm : ∀ k : κ, m (Sum.inr k) ≠ 0)
    (u : FreeSmoothRing (ι ⊕ κ)) :
    IsPartiallyHyperregular (natural m u) (naturalInverse m) where
  left_inv := FreeSmoothRing.hom_ext fun a => by
    rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply]
    rcases a with a | i | k
    · change naturalInverse m (partialLegendre (natural m u) (RouthSpace.q a)) = RouthSpace.q a
      rw [partialLegendre_q, naturalInverse, VelocitySpace.q, lift_generator]
      rfl
    · change naturalInverse m (partialLegendre (natural m u) (RouthSpace.v i)) = RouthSpace.v i
      rw [partialLegendre_v, naturalInverse, VelocitySpace.v, lift_generator]
      rfl
    · change naturalInverse m (partialLegendre (natural m u) (RouthSpace.p k)) = RouthSpace.p k
      rw [partialLegendre_p, momentum_natural, SmoothRingHom.map_mul,
        SmoothRingHom.map_algebraMap, naturalInverse, VelocitySpace.v, lift_generator]
      change algebraMap ℝ (RouthSpace ι κ) (m (Sum.inr k)) *
        (algebraMap ℝ (RouthSpace ι κ) (m (Sum.inr k))⁻¹ * RouthSpace.p k) = RouthSpace.p k
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hm k), map_one, one_mul]
  right_inv := FreeSmoothRing.hom_ext fun a => by
    rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply]
    rcases a with a | i | k
    · change partialLegendre (natural m u) (naturalInverse m (VelocitySpace.q a)) =
        VelocitySpace.q a
      rw [naturalInverse, VelocitySpace.q, lift_generator]
      exact partialLegendre_q _ a
    · change partialLegendre (natural m u) (naturalInverse m (VelocitySpace.v (Sum.inl i))) =
        VelocitySpace.v (Sum.inl i)
      rw [naturalInverse, VelocitySpace.v, lift_generator]
      exact partialLegendre_v _ i
    · change partialLegendre (natural m u) (naturalInverse m (VelocitySpace.v (Sum.inr k))) =
        VelocitySpace.v (Sum.inr k)
      rw [naturalInverse, VelocitySpace.v, lift_generator]
      change partialLegendre (natural m u)
        (algebraMap ℝ (RouthSpace ι κ) (m (Sum.inr k))⁻¹ * RouthSpace.p k) = _
      rw [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, partialLegendre_p,
        momentum_natural, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (hm k), map_one, one_mul]
      rfl

end Routhian

end ProjectAInos.Mechanics

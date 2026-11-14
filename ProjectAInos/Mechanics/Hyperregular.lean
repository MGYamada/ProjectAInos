/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Legendre
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Legendre transformation of a hyperregular Lagrangian

Landau–Lifshitz §40 (Theorem 51 of the manuscript). A Lagrangian `L(q, v)` is
an element of the free C-infinity ring on the positions and the velocities.
Its Legendre transformation is the morphism `FL` from the phase space with
`qᵢ ↦ qᵢ` and `pᵢ ↦ ∂L/∂vᵢ`. `L` is hyperregular when `FL` has an inverse
morphism `G`; the Hamiltonian is then `H = G(E)` for the energy
`E = Σ vᵢ ∂L/∂vᵢ − L`.

* `IsHyperregular.inverseHessian_mul_hessian`: the matrix `∂²L/∂vᵢ∂vⱼ` is
  invertible.
* `IsHyperregular.legendre_partialDerivation_inr_hamiltonian`,
  `IsHyperregular.legendre_partialDerivation_inl_hamiltonian`:
  `FL(∂H/∂pᵢ) = vᵢ` and `FL(∂H/∂qᵢ) = −∂L/∂qᵢ`.
* `IsHyperregular.isTrajectory_iff_isSolution`: the trajectories of `H` are
  the solutions of the Euler–Lagrange equations of `L` together with the
  momenta `pᵢ = ∂L/∂vᵢ`.
* `IsHyperregular.lagrangeBracket_q_v`: for the bracket transported to the
  functions of the positions and the velocities, `{qᵢ, vⱼ}` is the inverse of
  the matrix `∂²L/∂vᵢ∂vⱼ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

namespace JetRing

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] {R : JetRing ι J}

theorem sum_mul_d_q_self (a : ι → J) (j : ι) (n : ℕ) :
    ∑ i, a i * R.d j n (R.q i n) = a j := by
  rw [Finset.sum_eq_single j]
  · rw [R.d_q_self, mul_one]
  · intro i _ hi
    rw [R.d_q_ne i n j n (fun h => hi (Prod.mk.inj h).1), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem sum_mul_d_q_of_ne (a : ι → J) (j : ι) {n l : ℕ} (h : n ≠ l) :
    ∑ i, a i * R.d j l (R.q i n) = 0 :=
  Finset.sum_eq_zero fun i _ => by
    rw [R.d_q_ne i n j l (fun h' => h (Prod.mk.inj h').2), mul_zero]

end JetRing

/-- The ring of functions of the positions and the velocities. -/
abbrev VelocitySpace (ι : Type*) := FreeSmoothRing (ι ⊕ ι)

namespace VelocitySpace

variable {ι : Type*}

/-- The position `qᵢ`. -/
def q (i : ι) : VelocitySpace ι := generator (Sum.inl i)

/-- The velocity `vᵢ`. -/
def v (i : ι) : VelocitySpace ι := generator (Sum.inr i)

variable [DecidableEq ι]

/-- The momentum `∂L/∂vᵢ`. -/
def momentum (L : VelocitySpace ι) (i : ι) : VelocitySpace ι :=
  partialDerivation (Sum.inr i) L

/-- The Legendre transformation `FL`: the morphism from the phase space with
`qᵢ ↦ qᵢ` and `pᵢ ↦ ∂L/∂vᵢ`. -/
def legendre (L : VelocitySpace ι) : SmoothRingHom (PhaseSpace ι) (VelocitySpace ι) :=
  FreeSmoothRing.lift (Sum.elim q (momentum L))

@[simp] theorem legendre_q (L : VelocitySpace ι) (i : ι) :
    legendre L (PhaseSpace.q i) = q i := by
  rw [legendre, PhaseSpace.q, lift_generator, Sum.elim_inl]

@[simp] theorem legendre_p (L : VelocitySpace ι) (i : ι) :
    legendre L (PhaseSpace.p i) = momentum L i := by
  rw [legendre, PhaseSpace.p, lift_generator, Sum.elim_inr]

variable [Fintype ι]

/-- The energy `Σ vᵢ ∂L/∂vᵢ − L`. -/
def energy (L : VelocitySpace ι) : VelocitySpace ι :=
  ∑ i, v i * momentum L i - L

/-- The matrix `∂²L/∂vᵢ∂vⱼ`. -/
def hessian (L : VelocitySpace ι) : Matrix ι ι (VelocitySpace ι) :=
  Matrix.of fun i j => partialDerivation (Sum.inr j) (momentum L i)

/-- The chain rule for the Legendre transformation. -/
theorem apply_legendre (L : VelocitySpace ι)
    (E : SmoothDerivation (VelocitySpace ι) (VelocitySpace ι)) (s : PhaseSpace ι) :
    E (legendre L s) =
      ∑ i, legendre L (partialDerivation (Sum.inl i) s) * E (q i) +
        ∑ i, legendre L (partialDerivation (Sum.inr i) s) * E (momentum L i) := by
  rw [legendre, derivation_lift_mul, Fintype.sum_sum_type]
  rfl

theorem partialDerivation_inr_legendre (L : VelocitySpace ι) (s : PhaseSpace ι) (j : ι) :
    partialDerivation (Sum.inr j) (legendre L s) =
      ∑ i, legendre L (partialDerivation (Sum.inr i) s) * hessian L i j := by
  rw [apply_legendre, Finset.sum_eq_zero, zero_add]
  · rfl
  · intro i _
    rw [q, partialDerivation_generator_of_ne (by simp), mul_zero]

theorem partialDerivation_inl_legendre (L : VelocitySpace ι) (s : PhaseSpace ι) (j : ι) :
    partialDerivation (Sum.inl j) (legendre L s) =
      legendre L (partialDerivation (Sum.inl j) s) +
        ∑ i, legendre L (partialDerivation (Sum.inr i) s) *
          partialDerivation (Sum.inl j) (momentum L i) := by
  rw [apply_legendre, Finset.sum_eq_single j]
  · rw [q, partialDerivation_generator_self, mul_one]
  · intro i _ hi
    rw [q, partialDerivation_generator_of_ne (fun h => hi (Sum.inl.inj h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `∂E/∂vⱼ = Σᵢ vᵢ ∂²L/∂vᵢ∂vⱼ`. -/
theorem partialDerivation_inr_energy (L : VelocitySpace ι) (j : ι) :
    partialDerivation (Sum.inr j) (energy L) = ∑ i, v i * hessian L i j := by
  have h (i : ι) : partialDerivation (Sum.inr j) (v i * momentum L i) =
      v i * hessian L i j + if i = j then momentum L i else 0 := by
    rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul, v, partialDerivation_generator]
    simp only [Sum.inr.injEq, mul_ite, mul_one, mul_zero]
    rfl
  rw [energy, map_sub, map_sum]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact add_sub_cancel_right _ _

/-- `∂E/∂qⱼ = Σᵢ vᵢ ∂²L/∂qⱼ∂vᵢ − ∂L/∂qⱼ`. -/
theorem partialDerivation_inl_energy (L : VelocitySpace ι) (j : ι) :
    partialDerivation (Sum.inl j) (energy L) =
      ∑ i, v i * partialDerivation (Sum.inl j) (momentum L i) -
        partialDerivation (Sum.inl j) L := by
  rw [energy, map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul, v,
    partialDerivation_generator_of_ne (by simp), mul_zero, add_zero]

/-- `L` is hyperregular, with the inverse `G` of its Legendre
transformation. -/
structure IsHyperregular (L : VelocitySpace ι)
    (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)) : Prop where
  left_inv : G.comp (legendre L) = SmoothRingHom.id (PhaseSpace ι)
  right_inv : (legendre L).comp G = SmoothRingHom.id (VelocitySpace ι)

/-- The Hamiltonian `H = G(E)` of a hyperregular Lagrangian. -/
def hamiltonian (L : VelocitySpace ι) (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)) :
    PhaseSpace ι :=
  G (energy L)

/-- The matrix `FL(∂(G vₖ)/∂pᵢ)`, the inverse of the matrix `∂²L/∂vᵢ∂vⱼ`. -/
def inverseHessian (L : VelocitySpace ι) (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)) :
    Matrix ι ι (VelocitySpace ι) :=
  Matrix.of fun k i => legendre L (partialDerivation (Sum.inr i) (G (v k)))

namespace IsHyperregular

variable {L : VelocitySpace ι} {G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)}

omit [Fintype ι] in
theorem apply_legendre (h : IsHyperregular L G) (s : PhaseSpace ι) : G (legendre L s) = s :=
  congrArg (fun φ : SmoothRingHom (PhaseSpace ι) (PhaseSpace ι) => φ s) h.left_inv

omit [Fintype ι] in
theorem legendre_apply (h : IsHyperregular L G) (x : VelocitySpace ι) : legendre L (G x) = x :=
  congrArg (fun φ : SmoothRingHom (VelocitySpace ι) (VelocitySpace ι) => φ x) h.right_inv

/-- The Legendre transformation takes the Hamiltonian to the energy. -/
theorem legendre_hamiltonian (h : IsHyperregular L G) :
    legendre L (hamiltonian L G) = energy L :=
  h.legendre_apply _

omit [Fintype ι] in
theorem apply_q (h : IsHyperregular L G) (i : ι) : G (q i) = PhaseSpace.q i := by
  rw [← legendre_q L, h.apply_legendre]

omit [Fintype ι] in
theorem apply_momentum (h : IsHyperregular L G) (i : ι) : G (momentum L i) = PhaseSpace.p i := by
  rw [← legendre_p L, h.apply_legendre]

/-- The matrix `∂²L/∂vᵢ∂vⱼ` of a hyperregular Lagrangian is invertible. -/
theorem inverseHessian_mul_hessian (h : IsHyperregular L G) :
    inverseHessian L G * hessian L = 1 := by
  refine Matrix.ext fun k j => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h1 := partialDerivation_inr_legendre L (G (v k)) j
  rw [h.legendre_apply, v, partialDerivation_generator] at h1
  simp only [Sum.inr.injEq] at h1
  exact h1.symm

theorem hessian_mul_inverseHessian (h : IsHyperregular L G) :
    hessian L * inverseHessian L G = 1 :=
  mul_eq_one_comm.mp h.inverseHessian_mul_hessian

theorem eq_zero_of_vecMul_hessian (h : IsHyperregular L G) {x : ι → VelocitySpace ι}
    (hx : x ᵥ* hessian L = 0) : x = 0 := by
  calc x = x ᵥ* (hessian L * inverseHessian L G) := by
        rw [h.hessian_mul_inverseHessian, Matrix.vecMul_one]
    _ = (x ᵥ* hessian L) ᵥ* inverseHessian L G := (Matrix.vecMul_vecMul x _ _).symm
    _ = 0 := by rw [hx, Matrix.zero_vecMul]

/-- `FL(∂H/∂pᵢ) = vᵢ`. -/
theorem legendre_partialDerivation_inr_hamiltonian (h : IsHyperregular L G) (i : ι) :
    legendre L (partialDerivation (Sum.inr i) (hamiltonian L G)) = v i := by
  have hx : (fun i => legendre L (partialDerivation (Sum.inr i) (hamiltonian L G)) - v i) = 0 :=
    h.eq_zero_of_vecMul_hessian (funext fun j => by
      change ∑ i, (legendre L (partialDerivation (Sum.inr i) (hamiltonian L G)) - v i) *
        hessian L i j = 0
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [← partialDerivation_inr_legendre, ← partialDerivation_inr_energy,
        h.legendre_hamiltonian, sub_self])
  exact sub_eq_zero.mp (congrFun hx i)

/-- `FL(∂H/∂qⱼ) = −∂L/∂qⱼ`. -/
theorem legendre_partialDerivation_inl_hamiltonian (h : IsHyperregular L G) (j : ι) :
    legendre L (partialDerivation (Sum.inl j) (hamiltonian L G)) =
      -partialDerivation (Sum.inl j) L := by
  have h1 := partialDerivation_inl_legendre L (hamiltonian L G) j
  rw [h.legendre_hamiltonian, partialDerivation_inl_energy] at h1
  simp only [h.legendre_partialDerivation_inr_hamiltonian] at h1
  linear_combination -h1

/-- `G(vᵢ) = ∂H/∂pᵢ`. -/
theorem apply_v (h : IsHyperregular L G) (i : ι) :
    G (v i) = partialDerivation (Sum.inr i) (hamiltonian L G) := by
  rw [← h.legendre_partialDerivation_inr_hamiltonian i, h.apply_legendre]

/-- `G(∂L/∂qᵢ) = −∂H/∂qᵢ`. -/
theorem apply_partialDerivation_inl (h : IsHyperregular L G) (i : ι) :
    G (partialDerivation (Sum.inl i) L) = -partialDerivation (Sum.inl i) (hamiltonian L G) := by
  have h1 := congrArg G (h.legendre_partialDerivation_inl_hamiltonian i)
  rw [h.apply_legendre, SmoothRingHom.map_neg] at h1
  rw [h1, neg_neg]

end IsHyperregular

/-! ### Curves -/

omit [DecidableEq ι] [Fintype ι] in
/-- The curve of the positions and the velocities of a path. -/
def velocityCurve (γ : ι → TimeFunction) : ι ⊕ ι → TimeFunction :=
  Sum.elim γ fun i => timeDerivative (γ i)

omit [Fintype ι] in
/-- A function of the positions and the velocities, as an element of the jet
ring. -/
def toJet : SmoothRingHom (VelocitySpace ι) (StandardJet ι) :=
  FreeSmoothRing.lift
    (Sum.elim (fun i => (StandardJet.jetRing ι).q i 0) fun i => (StandardJet.jetRing ι).q i 1)

omit [Fintype ι] in
/-- A function of the positions and the velocities along a path. -/
theorem prolongation_toJet (γ : ι → TimeFunction) (s : VelocitySpace ι) :
    StandardJet.prolongation γ (toJet s) = FreeSmoothRing.lift (velocityCurve γ) s := by
  have h : (StandardJet.prolongation γ).comp toJet = FreeSmoothRing.lift (velocityCurve γ) :=
    FreeSmoothRing.hom_ext fun a => by
      rw [SmoothRingHom.comp_apply, toJet, lift_generator, lift_generator]
      rcases a with i | i
      · exact StandardJet.prolongation_q γ i 0
      · exact StandardJet.prolongation_q γ i 1
  exact congrArg (fun φ : SmoothRingHom (VelocitySpace ι) TimeFunction => φ s) h

/-- The chain rule for a function of the positions and the velocities in the
jet ring. -/
theorem apply_toJet (E : SmoothDerivation (StandardJet ι) (StandardJet ι))
    (s : VelocitySpace ι) :
    E (toJet s) =
      ∑ i, toJet (partialDerivation (Sum.inl i) s) * E ((StandardJet.jetRing ι).q i 0) +
        ∑ i, toJet (partialDerivation (Sum.inr i) s) * E ((StandardJet.jetRing ι).q i 1) := by
  rw [toJet, derivation_lift_mul, Fintype.sum_sum_type]
  rfl

theorem d_zero_toJet (s : VelocitySpace ι) (j : ι) :
    (StandardJet.jetRing ι).d j 0 (toJet s) = toJet (partialDerivation (Sum.inl j) s) := by
  rw [apply_toJet, JetRing.sum_mul_d_q_self, JetRing.sum_mul_d_q_of_ne _ j (by omega), add_zero]

theorem d_one_toJet (s : VelocitySpace ι) (j : ι) :
    (StandardJet.jetRing ι).d j 1 (toJet s) = toJet (partialDerivation (Sum.inr j) s) := by
  rw [apply_toJet, JetRing.sum_mul_d_q_self, JetRing.sum_mul_d_q_of_ne _ j (by omega), zero_add]

/-- A function of the positions and the velocities has order at most one. -/
theorem orderLE_toJet (s : VelocitySpace ι) : (StandardJet.jetRing ι).OrderLE (toJet s) 1 :=
  fun j k hk => by
    rw [apply_toJet, JetRing.sum_mul_d_q_of_ne _ j (by omega),
      JetRing.sum_mul_d_q_of_ne _ j (by omega), add_zero]

/-- The solutions of the Euler–Lagrange equations of `L(q, v)`:
`d/dt (∂L/∂vᵢ) = ∂L/∂qᵢ` along the path. -/
theorem isSolution_toJet_iff (L : VelocitySpace ι) (γ : ι → TimeFunction) :
    StandardJet.IsSolution (toJet L) γ ↔
      ∀ i, timeDerivative (FreeSmoothRing.lift (velocityCurve γ) (momentum L i)) =
        FreeSmoothRing.lift (velocityCurve γ) (partialDerivation (Sum.inl i) L) := by
  refine forall_congr' fun i => ?_
  rw [JetRing.euler_of_orderLE_one (orderLE_toJet L), JetRing.momentum, d_zero_toJet,
    d_one_toJet, SmoothRingHom.map_sub, StandardJet.prolongation_totalDeriv, prolongation_toJet,
    prolongation_toJet, sub_eq_zero, eq_comm]
  rfl

omit [Fintype ι] in
/-- Along a curve of the phase space with the momenta `pᵢ = ∂L/∂vᵢ`, the
Legendre transformation is the identity. -/
theorem lift_velocityCurve_legendre (L : VelocitySpace ι) {c : ι ⊕ ι → TimeFunction}
    (hm : ∀ i, c (Sum.inr i) =
      FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (momentum L i))
    (s : PhaseSpace ι) :
    FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (legendre L s) =
      FreeSmoothRing.lift c s := by
  have h : (FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i))).comp (legendre L) =
      FreeSmoothRing.lift c :=
    FreeSmoothRing.hom_ext fun a => by
      rw [SmoothRingHom.comp_apply, lift_generator]
      rcases a with i | i
      · change FreeSmoothRing.lift _ (legendre L (PhaseSpace.q i)) = c (Sum.inl i)
        rw [legendre_q, q, lift_generator]
        rfl
      · change FreeSmoothRing.lift _ (legendre L (PhaseSpace.p i)) = c (Sum.inr i)
        rw [legendre_p, hm i]
  exact congrArg (fun φ : SmoothRingHom (PhaseSpace ι) TimeFunction => φ s) h

namespace IsHyperregular

variable {L : VelocitySpace ι} {G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)}

/-- Along a curve of the phase space with `q̇ᵢ = ∂H/∂pᵢ`, the inverse of the
Legendre transformation is the identity. -/
theorem lift_apply (h : IsHyperregular L G) {c : ι ⊕ ι → TimeFunction}
    (hq : ∀ i, timeDerivative (c (Sum.inl i)) =
      FreeSmoothRing.lift c (partialDerivation (Sum.inr i) (hamiltonian L G)))
    (x : VelocitySpace ι) :
    FreeSmoothRing.lift c (G x) =
      FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) x := by
  have hc : (FreeSmoothRing.lift c).comp G =
      FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) :=
    FreeSmoothRing.hom_ext fun a => by
      rw [SmoothRingHom.comp_apply, lift_generator]
      rcases a with i | i
      · change FreeSmoothRing.lift c (G (q i)) = c (Sum.inl i)
        rw [h.apply_q, PhaseSpace.q, lift_generator]
      · change FreeSmoothRing.lift c (G (v i)) = timeDerivative (c (Sum.inl i))
        rw [h.apply_v, hq i]
  exact congrArg (fun φ : SmoothRingHom (VelocitySpace ι) TimeFunction => φ x) hc

/-- The Legendre correspondence along curves: the trajectories of `H` are the
curves with `d/dt (∂L/∂vᵢ) = ∂L/∂qᵢ` and `pᵢ = ∂L/∂vᵢ`. -/
theorem isTrajectory_iff (h : IsHyperregular L G) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical ι) (hamiltonian L G) c ↔
      (∀ i, timeDerivative
          (FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (momentum L i)) =
        FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i))
          (partialDerivation (Sum.inl i) L)) ∧
      ∀ i, c (Sum.inr i) =
        FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (momentum L i) := by
  rw [isTrajectory_canonical_iff]
  constructor
  · rintro ⟨hq, hp⟩
    have hG := h.lift_apply hq
    have hm (i : ι) : c (Sum.inr i) =
        FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (momentum L i) := by
      rw [← hG, h.apply_momentum, PhaseSpace.p, lift_generator]
    refine ⟨fun i => ?_, hm⟩
    rw [← hm i, hp i, ← hG, h.apply_partialDerivation_inl, SmoothRingHom.map_neg]
  · rintro ⟨hEL, hm⟩
    have hF := lift_velocityCurve_legendre L hm
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← hF, h.legendre_partialDerivation_inr_hamiltonian, v, lift_generator]
      rfl
    · rw [← hF, h.legendre_partialDerivation_inl_hamiltonian, SmoothRingHom.map_neg, neg_neg,
        ← hEL i, ← hm i]

/-- The Legendre correspondence (Landau–Lifshitz §40, Theorem 51): the
trajectories of the Hamiltonian of a hyperregular Lagrangian are the solutions
of its Euler–Lagrange equations together with the momenta `pᵢ = ∂L/∂vᵢ`. -/
theorem isTrajectory_iff_isSolution (h : IsHyperregular L G) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical ι) (hamiltonian L G) c ↔
      StandardJet.IsSolution (toJet L) (fun i => c (Sum.inl i)) ∧
        ∀ i, c (Sum.inr i) =
          FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (momentum L i) := by
  rw [h.isTrajectory_iff, isSolution_toJet_iff]

end IsHyperregular

/-! ### The bracket of the functions of the positions and the velocities -/

/-- The canonical bracket transported to the functions of the positions and
the velocities by the Legendre transformation. -/
def lagrangeBracket (L : VelocitySpace ι) (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι))
    (f g : VelocitySpace ι) : VelocitySpace ι :=
  legendre L ((PhaseSpace.canonical ι).bracket (G f) (G g))

namespace IsHyperregular

variable {L : VelocitySpace ι} {G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)}

/-- The Legendre transformation takes the canonical bracket to the
transported bracket. -/
theorem legendre_bracket (h : IsHyperregular L G) (f g : PhaseSpace ι) :
    legendre L ((PhaseSpace.canonical ι).bracket f g) =
      lagrangeBracket L G (legendre L f) (legendre L g) := by
  rw [lagrangeBracket, h.apply_legendre, h.apply_legendre]

theorem lagrangeBracket_q_q (h : IsHyperregular L G) (i j : ι) :
    lagrangeBracket L G (q i) (q j) = 0 := by
  rw [lagrangeBracket, h.apply_q, h.apply_q, PhaseSpace.canonical_q_q, SmoothRingHom.map_zero]

/-- `{qᵢ, vⱼ}` is the inverse of the matrix `∂²L/∂vᵢ∂vⱼ`. -/
theorem lagrangeBracket_q_v (h : IsHyperregular L G) (i j : ι) :
    lagrangeBracket L G (q i) (v j) = inverseHessian L G j i := by
  rw [lagrangeBracket, h.apply_q, PhaseSpace.canonical_q_bracket]
  rfl

/-- The energy generates the motion: `{qᵢ, E} = vᵢ`. -/
theorem lagrangeBracket_q_energy (h : IsHyperregular L G) (i : ι) :
    lagrangeBracket L G (q i) (energy L) = v i := by
  rw [lagrangeBracket, h.apply_q, PhaseSpace.canonical_q_bracket]
  exact h.legendre_partialDerivation_inr_hamiltonian i

end IsHyperregular

/-! ### Natural Lagrangians -/

/-- The natural Lagrangian `Σ ½ mᵢ vᵢ² − U(q)` as a function of the positions
and the velocities. -/
def natural (m : ι → ℝ) (u : FreeSmoothRing ι) : VelocitySpace ι :=
  ∑ i, algebraMap ℝ (VelocitySpace ι) (m i / 2) * (v i * v i) - positionsToPhase u

/-- The inverse of the Legendre transformation of a natural Lagrangian:
`qᵢ ↦ qᵢ`, `vᵢ ↦ pᵢ / mᵢ`. -/
def naturalInverse (m : ι → ℝ) : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι) :=
  FreeSmoothRing.lift
    (Sum.elim PhaseSpace.q fun i => algebraMap ℝ (PhaseSpace ι) (m i)⁻¹ * PhaseSpace.p i)

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem naturalInverse_q (m : ι → ℝ) (i : ι) :
    naturalInverse m (q i) = PhaseSpace.q i := by
  rw [naturalInverse, q, lift_generator, Sum.elim_inl]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem naturalInverse_v (m : ι → ℝ) (i : ι) :
    naturalInverse m (v i) = algebraMap ℝ (PhaseSpace ι) (m i)⁻¹ * PhaseSpace.p i := by
  rw [naturalInverse, v, lift_generator, Sum.elim_inr]

omit [DecidableEq ι] [Fintype ι] in
theorem naturalInverse_positionsToPhase (m : ι → ℝ) (u : FreeSmoothRing ι) :
    naturalInverse m (positionsToPhase u) = positionsToPhase u := by
  have h : (naturalInverse m).comp positionsToPhase = positionsToPhase :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, positionsToPhase, lift_generator]
      exact naturalInverse_q m i
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) (PhaseSpace ι) => φ u) h

/-- The momenta of a natural Lagrangian are `pᵢ = mᵢ vᵢ`. -/
theorem momentum_natural (m : ι → ℝ) (u : FreeSmoothRing ι) (j : ι) :
    momentum (natural m u) j = algebraMap ℝ (VelocitySpace ι) (m j) * v j := by
  rw [momentum, natural, map_sub, partialDerivation_inr_positionsToPhase, sub_zero, map_sum,
    Finset.sum_eq_single j]
  · rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, v,
      partialDerivation_generator_self,
      ← JetRing.algebraMap_half_mul_two (J := VelocitySpace ι) (m j)]
    simp only [smul_eq_mul, mul_one]
    ring
  · intro i _ hi
    rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, v,
      partialDerivation_generator_of_ne (fun h => hi (Sum.inr.inj h)), smul_zero, add_zero,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- A natural Lagrangian with non-zero masses is hyperregular. -/
theorem isHyperregular_natural {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) :
    IsHyperregular (natural m u) (naturalInverse m) where
  left_inv := FreeSmoothRing.hom_ext fun a => by
    rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply]
    rcases a with i | i
    · change naturalInverse m (legendre (natural m u) (PhaseSpace.q i)) = PhaseSpace.q i
      rw [legendre_q, naturalInverse_q]
    · change naturalInverse m (legendre (natural m u) (PhaseSpace.p i)) = PhaseSpace.p i
      rw [legendre_p, momentum_natural, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
        naturalInverse_v, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (hm i), map_one, one_mul]
  right_inv := FreeSmoothRing.hom_ext fun a => by
    rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply]
    rcases a with i | i
    · change legendre (natural m u) (naturalInverse m (q i)) = q i
      rw [naturalInverse_q, legendre_q]
    · change legendre (natural m u) (naturalInverse m (v i)) = v i
      rw [naturalInverse_v, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, legendre_p,
        momentum_natural, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (hm i), map_one, one_mul]

/-- The energy of a natural Lagrangian is `Σ ½ mᵢ vᵢ² + U(q)`. -/
theorem energy_natural (m : ι → ℝ) (u : FreeSmoothRing ι) :
    energy (natural m u) =
      ∑ i, algebraMap ℝ (VelocitySpace ι) (m i / 2) * (v i * v i) + positionsToPhase u := by
  have hterm (i : ι) : v i * momentum (natural m u) i =
      algebraMap ℝ (VelocitySpace ι) (m i / 2) * (v i * v i) +
        algebraMap ℝ (VelocitySpace ι) (m i / 2) * (v i * v i) := by
    rw [momentum_natural, ← JetRing.algebraMap_half_mul_two (J := VelocitySpace ι) (m i)]
    ring
  rw [energy]
  simp only [hterm, Finset.sum_add_distrib]
  rw [natural]
  ring

/-- The Hamiltonian of a natural Lagrangian is `Σ pᵢ² / 2mᵢ + U(q)`. -/
theorem hamiltonian_natural {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) :
    hamiltonian (natural m u) (naturalInverse m) =
      PhaseSpace.kineticEnergy m + positionsToPhase u := by
  rw [hamiltonian, energy_natural, SmoothRingHom.map_add, SmoothRingHom.map_sum,
    naturalInverse_positionsToPhase, PhaseSpace.kineticEnergy]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : m i / 2 * ((m i)⁻¹ * (m i)⁻¹) = (m i)⁻¹ / 2 := by
    have h := mul_inv_cancel₀ (hm i)
    linear_combination ((m i)⁻¹ / 2) * h
  rw [SmoothRingHom.map_mul, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    naturalInverse_v, ← hr]
  simp only [map_mul]
  ring

omit [Fintype ι] in
theorem toJet_q (i : ι) : toJet (q i) = (StandardJet.jetRing ι).q i 0 := by
  rw [toJet, q, lift_generator, Sum.elim_inl]

omit [Fintype ι] in
theorem toJet_v (i : ι) : toJet (v i) = (StandardJet.jetRing ι).q i 1 := by
  rw [toJet, v, lift_generator, Sum.elim_inr]

omit [Fintype ι] in
/-- A function of the positions, read in the jet ring through the functions of
the positions and the velocities. -/
theorem toJet_positionsToPhase (u : FreeSmoothRing ι) :
    toJet (positionsToPhase u) = positionsToJet u := by
  have h : (toJet (ι := ι)).comp positionsToPhase = positionsToJet :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, positionsToPhase, positionsToJet, lift_generator,
        lift_generator]
      exact toJet_q i
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) (StandardJet ι) => φ u) h

/-- In the jet ring, `natural m u` is the natural Lagrangian of
`Jet/Conservation`. -/
theorem toJet_natural (m : ι → ℝ) (u : FreeSmoothRing ι) :
    toJet (natural m u) = (StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u) := by
  rw [natural, JetRing.naturalLagrangian, SmoothRingHom.map_sub, SmoothRingHom.map_sum,
    toJet_positionsToPhase]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, toJet_v]

end VelocitySpace

end ProjectAInos.Mechanics

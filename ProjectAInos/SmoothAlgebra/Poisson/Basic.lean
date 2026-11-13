/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Derivation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Poisson structures on C-infinity rings

A Poisson structure on a C-infinity ring is a bracket that is antisymmetric,
satisfies the Jacobi identity, and is a C-infinity derivation in its first
argument. Additivity, the Leibniz rule and real bilinearity are consequences of
the chain rule, as for derivations.

The bracket is a field of a structure and not Mathlib's `Bracket` class: every
ring already carries the commutator as its `Bracket`, which vanishes on a
commutative ring. A structure also allows several Poisson structures on one
ring, such as the canonical and the Lie–Poisson brackets on a free ring.

An almost-Poisson structure omits the Jacobi identity. Its Jacobiator is a
C-infinity derivation in each argument; the proof uses the symmetry of second
partial derivatives. This reduces the Jacobi identity to generators.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra

open SmoothRing SmoothOperation

/-- An antisymmetric bracket that is a C-infinity derivation in its first
argument. The Jacobi identity is not assumed. -/
structure AlmostPoissonStructure (P : Type*) [CommRing P] [Algebra ℝ P] [SmoothRing P] where
  /-- The bracket. -/
  bracket : P → P → P
  /-- Antisymmetry. -/
  antisymm : ∀ f g, bracket f g = -bracket g f
  /-- The chain rule in the first argument, for every finite smooth operation. -/
  chain : ∀ {n} (f : SmoothOperation n) (c : Fin n → P) (h : P),
    bracket (op f c) h = ∑ i, op (partialDeriv i f) c * bracket (c i) h

namespace AlmostPoissonStructure

variable {P : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P] (π : AlmostPoissonStructure P)

/-- The vector field `X_h = {·, h}`. -/
def hamiltonian (h : P) : SmoothDerivation P P where
  toFun f := π.bracket f h
  chain' f c := by simpa only [smul_eq_mul] using π.chain f c h

@[simp] theorem hamiltonian_apply (h f : P) : π.hamiltonian h f = π.bracket f h := rfl

theorem bracket_add_left (f g h : P) :
    π.bracket (f + g) h = π.bracket f h + π.bracket g h := (π.hamiltonian h).map_add f g

theorem bracket_mul_left (f g h : P) :
    π.bracket (f * g) h = f * π.bracket g h + g * π.bracket f h :=
  (π.hamiltonian h).map_mul f g

@[simp] theorem bracket_algebraMap_left (r : ℝ) (h : P) :
    π.bracket (algebraMap ℝ P r) h = 0 := (π.hamiltonian h).map_algebraMap r

@[simp] theorem bracket_zero_left (h : P) : π.bracket 0 h = 0 := (π.hamiltonian h).map_zero

@[simp] theorem bracket_one_left (h : P) : π.bracket 1 h = 0 := (π.hamiltonian h).map_one

theorem bracket_neg_left (f h : P) : π.bracket (-f) h = -π.bracket f h :=
  map_neg (π.hamiltonian h) f

theorem bracket_sub_left (f g h : P) :
    π.bracket (f - g) h = π.bracket f h - π.bracket g h := map_sub (π.hamiltonian h) f g

theorem bracket_smul_left (r : ℝ) (f h : P) : π.bracket (r • f) h = r • π.bracket f h :=
  (π.hamiltonian h).map_smul r f

theorem bracket_sum_left {ι : Type*} (s : Finset ι) (f : ι → P) (h : P) :
    π.bracket (∑ i ∈ s, f i) h = ∑ i ∈ s, π.bracket (f i) h := map_sum (π.hamiltonian h) f s

theorem bracket_add_right (f g h : P) :
    π.bracket f (g + h) = π.bracket f g + π.bracket f h := by
  rw [π.antisymm, bracket_add_left, neg_add, ← π.antisymm, ← π.antisymm]

theorem bracket_mul_right (f g h : P) :
    π.bracket f (g * h) = g * π.bracket f h + h * π.bracket f g := by
  rw [π.antisymm, bracket_mul_left, π.antisymm h f, π.antisymm g f]
  ring

@[simp] theorem bracket_algebraMap_right (f : P) (r : ℝ) :
    π.bracket f (algebraMap ℝ P r) = 0 := by
  rw [π.antisymm, bracket_algebraMap_left, neg_zero]

@[simp] theorem bracket_zero_right (f : P) : π.bracket f 0 = 0 := by
  rw [π.antisymm, bracket_zero_left, neg_zero]

@[simp] theorem bracket_one_right (f : P) : π.bracket f 1 = 0 := by
  rw [π.antisymm, bracket_one_left, neg_zero]

theorem bracket_neg_right (f g : P) : π.bracket f (-g) = -π.bracket f g := by
  rw [π.antisymm, bracket_neg_left, ← π.antisymm]

theorem bracket_sub_right (f g h : P) :
    π.bracket f (g - h) = π.bracket f g - π.bracket f h := by
  rw [sub_eq_add_neg, bracket_add_right, bracket_neg_right, sub_eq_add_neg]

theorem bracket_smul_right (r : ℝ) (f g : P) : π.bracket f (r • g) = r • π.bracket f g := by
  rw [π.antisymm, bracket_smul_left, ← smul_neg, ← π.antisymm]

theorem bracket_sum_right {ι : Type*} (s : Finset ι) (f : P) (g : ι → P) :
    π.bracket f (∑ i ∈ s, g i) = ∑ i ∈ s, π.bracket f (g i) := by
  rw [π.antisymm, bracket_sum_left, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (π.antisymm f (g i)).symm

/-- The bracket of an element with itself vanishes. -/
@[simp] theorem bracket_self (f : P) : π.bracket f f = 0 := by
  have h : π.bracket f f + π.bracket f f = 0 := by
    nth_rewrite 1 [π.antisymm f f]
    exact neg_add_cancel _
  have h2 : (2 : ℝ) • π.bracket f f = 0 := by rw [two_smul, h]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The chain rule in the second argument. -/
theorem chain_right {n : ℕ} (f : SmoothOperation n) (c : Fin n → P) (h : P) :
    π.bracket h (op f c) = ∑ i, op (partialDeriv i f) c * π.bracket h (c i) := by
  rw [π.antisymm, π.chain, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [π.antisymm (c i) h]
  ring

/-- Brackets are determined by their values on generators. -/
theorem bracket_op_op {n m : ℕ} (f : SmoothOperation n) (g : SmoothOperation m)
    (a : Fin n → P) (b : Fin m → P) :
    π.bracket (op f a) (op g b) =
      ∑ i, ∑ j, op (partialDeriv i f) a * op (partialDeriv j g) b * π.bracket (a i) (b j) := by
  rw [π.chain]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [π.chain_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The Jacobiator of the bracket. -/
def jacobiator (f g h : P) : P :=
  π.bracket (π.bracket f g) h + π.bracket (π.bracket g h) f + π.bracket (π.bracket h f) g

theorem jacobiator_cyclic (f g h : P) : π.jacobiator f g h = π.jacobiator g h f := by
  unfold jacobiator
  abel

/-- The Jacobiator satisfies the chain rule in its first argument. The
second-order terms cancel because partial derivatives commute. -/
theorem jacobiator_op {n : ℕ} (f : SmoothOperation n) (c : Fin n → P) (g h : P) :
    π.jacobiator (op f c) g h = ∑ i, op (partialDeriv i f) c * π.jacobiator (c i) g h := by
  have h1 : π.bracket (π.bracket (op f c) g) h =
      ∑ i, op (partialDeriv i f) c * π.bracket (π.bracket (c i) g) h +
        ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) c *
          (π.bracket (c j) h * π.bracket (c i) g) := by
    rw [π.chain, bracket_sum_left, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bracket_mul_left, π.chain, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : π.bracket (π.bracket h (op f c)) g =
      ∑ i, op (partialDeriv i f) c * π.bracket (π.bracket h (c i)) g -
        ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) c *
          (π.bracket (c j) g * π.bracket (c i) h) := by
    rw [π.chain_right, bracket_sum_left, sub_eq_add_neg, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bracket_mul_left, π.chain, Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [π.antisymm h (c i)]
    ring
  have h2 : π.bracket (π.bracket g h) (op f c) =
      ∑ i, op (partialDeriv i f) c * π.bracket (π.bracket g h) (c i) := π.chain_right f c _
  have hswap : ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) c *
        (π.bracket (c j) g * π.bracket (c i) h) =
      ∑ i, ∑ j, op (partialDeriv j (partialDeriv i f)) c *
        (π.bracket (c j) h * π.bracket (c i) g) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [partialDeriv_comm i j f]
    ring
  unfold jacobiator
  rw [h1, h2, h3, hswap]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- The bracket `{f, g} = Σ_{a,b} Dₐf D_b g w a b` of a finite family of vector
fields `D` and a skew matrix `w` of elements. It is an almost-Poisson
structure; the Jacobi identity is a condition on `D` and `w`. -/
def ofDerivations {κ : Type*} [Fintype κ] (D : κ → SmoothDerivation P P) (w : κ → κ → P)
    (hw : ∀ a b, w a b = -w b a) : AlmostPoissonStructure P where
  bracket f g := ∑ a, ∑ b, D a f * D b g * w a b
  antisymm f g := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hw b a]
    ring
  chain f c h := by
    have hterm (a b : κ) : D a (op f c) * D b h * w a b =
        ∑ i, op (partialDeriv i f) c * (D a (c i) * D b h * w a b) := by
      rw [SmoothDerivation.chain, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by
        rw [smul_eq_mul]
        ring
    simp only [hterm, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    exact Finset.sum_comm

@[simp] theorem ofDerivations_bracket {κ : Type*} [Fintype κ] (D : κ → SmoothDerivation P P)
    (w : κ → κ → P) (hw : ∀ a b, w a b = -w b a) (f g : P) :
    (ofDerivations D w hw).bracket f g = ∑ a, ∑ b, D a f * D b g * w a b := rfl

end AlmostPoissonStructure

/-- A Poisson structure on a C-infinity ring: an antisymmetric bracket that
satisfies the Jacobi identity and the chain rule in its first argument. -/
structure PoissonStructure (P : Type*) [CommRing P] [Algebra ℝ P] [SmoothRing P]
    extends AlmostPoissonStructure P where
  /-- The Jacobi identity. -/
  jacobi : ∀ f g h,
    bracket (bracket f g) h + bracket (bracket g h) f + bracket (bracket h f) g = 0

namespace PoissonStructure

variable {P : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P] (π : PoissonStructure P)

/-- The Jacobi identity as a derivation property of the bracket:
`{{f, g}, h} = {{f, h}, g} + {f, {g, h}}`. The Hamiltonian vector field `X_h`
is a derivation of the bracket, so the motion is canonical. -/
theorem bracket_bracket (f g h : P) :
    π.bracket (π.bracket f g) h =
      π.bracket (π.bracket f h) g + π.bracket f (π.bracket g h) := by
  have hj := π.jacobi f g h
  have h1 : π.bracket (π.bracket g h) f = -π.bracket f (π.bracket g h) := π.antisymm _ _
  have h2 : π.bracket (π.bracket h f) g = -π.bracket (π.bracket f h) g := by
    rw [π.antisymm h f, π.toAlmostPoissonStructure.bracket_neg_left]
  rw [h1, h2] at hj
  linear_combination hj

/-- `X_{f, g} = −[X_f, X_g]`: Hamiltonian vector fields form a Lie subring, with
the sign fixed by the convention `X_h = {·, h}`. -/
theorem hamiltonian_bracket (f g : P) :
    π.hamiltonian (π.bracket f g) = -⁅π.hamiltonian f, π.hamiltonian g⁆ := by
  refine SmoothDerivation.ext fun k => ?_
  rw [SmoothDerivation.neg_apply, SmoothDerivation.commutator_apply]
  simp only [AlmostPoissonStructure.hamiltonian_apply]
  have hj := π.jacobi k f g
  have h1 : π.bracket (π.bracket f g) k = -π.bracket k (π.bracket f g) := π.antisymm _ _
  have h2 : π.bracket (π.bracket g k) f = -π.bracket (π.bracket k g) f := by
    rw [π.antisymm g k, π.toAlmostPoissonStructure.bracket_neg_left]
  rw [h1, h2] at hj
  linear_combination -hj

/-- `f` is an integral of the motion of the Hamiltonian `H`. -/
def IsIntegral (H f : P) : Prop := π.bracket f H = 0

variable {π}

/-- The Hamiltonian is an integral of its own motion. -/
theorem isIntegral_self (H : P) : π.IsIntegral H H :=
  π.toAlmostPoissonStructure.bracket_self H

/-- Poisson's theorem (Landau–Lifshitz §42): the bracket of two integrals of the
motion is an integral of the motion. -/
theorem IsIntegral.bracket {H f g : P} (hf : π.IsIntegral H f) (hg : π.IsIntegral H g) :
    π.IsIntegral H (π.bracket f g) := by
  unfold IsIntegral at *
  rw [π.bracket_bracket, hf, hg]
  simp

/-- A smooth function of integrals of the motion is an integral of the motion. -/
theorem IsIntegral.op {H : P} {n : ℕ} (f : SmoothOperation n) {c : Fin n → P}
    (hc : ∀ i, π.IsIntegral H (c i)) : π.IsIntegral H (op f c) := by
  unfold IsIntegral at *
  rw [π.chain]
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, mul_zero]

variable (π) in
/-- The integrals of the motion form a real subalgebra. It is also closed under
the bracket and under every smooth operation. -/
def integrals (H : P) : Subalgebra ℝ P where
  carrier := {f | π.IsIntegral H f}
  mul_mem' {f g} hf hg := by
    change π.bracket (f * g) H = 0
    rw [π.toAlmostPoissonStructure.bracket_mul_left, hf, hg]
    simp
  add_mem' {f g} hf hg := by
    change π.bracket (f + g) H = 0
    rw [π.toAlmostPoissonStructure.bracket_add_left, hf, hg, add_zero]
  algebraMap_mem' r := π.toAlmostPoissonStructure.bracket_algebraMap_left r H

/-- Noether's theorem in Hamiltonian form (Landau–Lifshitz §§6–9): `μ` is an
integral of the motion of `H` exactly when `H` is invariant under the
Hamiltonian vector field of `μ`. -/
theorem isIntegral_iff_hamiltonian_eq_zero (H μ : P) :
    π.IsIntegral H μ ↔ π.hamiltonian μ H = 0 := by
  unfold IsIntegral
  rw [AlmostPoissonStructure.hamiltonian_apply, π.antisymm H μ, neg_eq_zero]

end PoissonStructure

end ProjectAInos.SmoothAlgebra

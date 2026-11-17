/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Poisson.OrbitalCharge
public import ProjectAinos.SmoothAlgebra.RelEnergy
public import ProjectAinos.SmoothGeometry.Minkowski.Matrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The Poincaré algebra of the orbital charges

**Covariant form.** On the canonical phase space of an event `x` and its momentum covector `p`
the charges of the translations are the momenta `p_μ`, and the charges of the Lorentz
transformations are `lorentzCharge σ d μ ν = x_μ p_ν − x_ν p_μ`, with the index of `x` lowered
by the Minkowski metric `η` of the convention `σ`. Their brackets are

* `{p_μ, p_ν} = 0` (`PhaseSpace.canonical_p_p`),
* `canonical_lorentzCharge_p`: `{J_μν, p_ρ} = η_μρ p_ν − η_νρ p_μ`,
* `canonical_lorentzCharge_lorentzCharge`:
  `{J_μν, J_ρσ} = η_μρ J_νσ − η_νρ J_μσ + η_νσ J_μρ − η_μσ J_νρ`,

and the charges have zero bracket with `η⁻¹(p, p)`
(`canonical_lorentzCharge_momentumQuadratic`).

**Initial data, with the speed of light.** On the phase space of `d` space coordinates and with
`ε = 1/c`, the function `inertia d m ε = √(m² + ε² Σ pᵢ²)` is the energy divided by `c²`. The
charges are the momenta `pᵢ`, the angular momenta `angularMomentum d i j = qᵢ pⱼ − qⱼ pᵢ`, and
the boost charges `boostCharge d m ε i = inertia · qᵢ` at time zero. For every real `ε`

* `canonical_boostCharge_p`: `{Kᵢ, pⱼ} = δᵢⱼ · inertia`,
* `canonical_boostCharge_boostCharge`: `{Kᵢ, Kⱼ} = −ε² Mᵢⱼ`,
* `canonical_boostCharge_inertia`: `{Kᵢ, inertia} = ε² pᵢ`,
* `canonical_angularMomentum_boostCharge`: `{Mᵢⱼ, Kₖ} = δₖᵢ Kⱼ − δₖⱼ Kᵢ`.

At `ε = 0` the inertia is the mass (`inertia_zero`): the boosts commute and `{Kᵢ, pⱼ} = m δᵢⱼ`,
which are the relations of the Galilei algebra with the mass as its central term. At `ε = 1`
the inertia is the energy of the units with `c = 1`.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity.Poincare

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace SmoothGeometry

variable {d : ℕ}

/-! ### Covariant form -/

/-- The charge `J_μν = x_μ p_ν − x_ν p_μ` of the Lorentz transformations. -/
def lorentzCharge (σ : LorentzConvention) (d : ℕ) (μ ν : Fin (d + 1)) :
    PhaseSpace (Fin (d + 1)) :=
  orbitalCharge (Minkowski.metricMatrix σ d) μ ν

/-- The charge in the coordinates: `J_μν = s_μ q_μ p_ν − s_ν q_ν p_μ` with the signs `s` of the
metric. -/
theorem lorentzCharge_eq (σ : LorentzConvention) (μ ν : Fin (d + 1)) :
    lorentzCharge σ d μ ν =
      lorentzSign σ μ • q μ * p ν - lorentzSign σ ν • q ν * p μ := by
  rw [lorentzCharge, orbitalCharge, Minkowski.metricMatrix, loweredCoordinate_diagonal,
    loweredCoordinate_diagonal]

theorem lorentzCharge_antisymm (σ : LorentzConvention) (μ ν : Fin (d + 1)) :
    lorentzCharge σ d μ ν = -lorentzCharge σ d ν μ :=
  orbitalCharge_antisymm _ μ ν

/-- The momenta transform as a covector: `{J_μν, p_ρ} = η_μρ p_ν − η_νρ p_μ`. -/
theorem canonical_lorentzCharge_p (σ : LorentzConvention) (μ ν ρ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (lorentzCharge σ d μ ν) (p ρ) =
      algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d μ ρ) * p ν -
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d ν ρ) * p μ :=
  canonical_orbitalCharge_p _ μ ν ρ

/-- The Lorentz algebra:
`{J_μν, J_ρτ} = η_μρ J_ντ − η_νρ J_μτ + η_ντ J_μρ − η_μτ J_νρ`. -/
theorem canonical_lorentzCharge_lorentzCharge (σ : LorentzConvention) (μ ν ρ τ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (lorentzCharge σ d μ ν) (lorentzCharge σ d ρ τ) =
      algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d μ ρ) *
          lorentzCharge σ d ν τ -
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d ν ρ) *
          lorentzCharge σ d μ τ +
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d ν τ) *
          lorentzCharge σ d μ ρ -
        algebraMap ℝ (PhaseSpace (Fin (d + 1))) (Minkowski.metricMatrix σ d μ τ) *
          lorentzCharge σ d ν ρ :=
  canonical_orbitalCharge_orbitalCharge (Minkowski.metricMatrix_isSymm σ) μ ν ρ τ

/-- The Lorentz charges are symmetries of `η⁻¹(p, p)`. -/
theorem canonical_lorentzCharge_momentumQuadratic (σ : LorentzConvention) (μ ν : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (lorentzCharge σ d μ ν)
      (momentumQuadratic (Minkowski.metricMatrix σ d)) = 0 :=
  canonical_orbitalCharge_momentumQuadratic (Minkowski.metricMatrix_isSymm σ)
    (Minkowski.metricMatrix_mul_self σ) μ ν

/-! ### Initial data, with the speed of light -/

/-- The angular momentum `Mᵢⱼ = qᵢ pⱼ − qⱼ pᵢ`. -/
def angularMomentum (d : ℕ) (i j : Fin d) : PhaseSpace (Fin d) :=
  orbitalCharge (1 : Matrix (Fin d) (Fin d) ℝ) i j

theorem loweredCoordinate_one (i : Fin d) :
    loweredCoordinate (1 : Matrix (Fin d) (Fin d) ℝ) i = q i := by
  rw [← Matrix.diagonal_one, loweredCoordinate_diagonal, one_smul]

theorem angularMomentum_eq (i j : Fin d) :
    angularMomentum d i j = q i * p j - q j * p i := by
  rw [angularMomentum, orbitalCharge, loweredCoordinate_one, loweredCoordinate_one]

/-- `{Mᵢⱼ, qₖ} = δₖᵢ qⱼ − δₖⱼ qᵢ`. -/
theorem canonical_angularMomentum_q (i j k : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (q k) =
      (if k = i then q j else 0) - if k = j then q i else 0 := by
  have h := canonical_orbitalCharge_loweredCoordinate (1 : Matrix (Fin d) (Fin d) ℝ) i j k
  rw [loweredCoordinate_one, loweredCoordinate_one, loweredCoordinate_one, Matrix.one_apply,
    Matrix.one_apply] at h
  rw [angularMomentum, h]
  split_ifs <;> simp

/-- `{Mᵢⱼ, pₖ} = δᵢₖ pⱼ − δⱼₖ pᵢ`. -/
theorem canonical_angularMomentum_p (i j k : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (p k) =
      (if i = k then p j else 0) - if j = k then p i else 0 := by
  rw [angularMomentum, canonical_orbitalCharge_p, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The rotation algebra: `{Mᵢⱼ, Mₖₗ} = δᵢₖ Mⱼₗ − δⱼₖ Mᵢₗ + δⱼₗ Mᵢₖ − δᵢₗ Mⱼₖ`. -/
theorem canonical_angularMomentum_angularMomentum (i j k l : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (angularMomentum d k l) =
      (if i = k then angularMomentum d j l else 0) -
          (if j = k then angularMomentum d i l else 0) +
        (if j = l then angularMomentum d i k else 0) -
        if i = l then angularMomentum d j k else 0 := by
  rw [angularMomentum, angularMomentum,
    canonical_orbitalCharge_orbitalCharge Matrix.isSymm_one, Matrix.one_apply, Matrix.one_apply,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [angularMomentum]

/-- `√(m² + ε² Σ pᵢ²)`: the energy divided by `c²`, with `ε = 1/c`. -/
def inertia (d : ℕ) (m ε : ℝ) : PhaseSpace (Fin d) :=
  relEnergy m fun i => algebraMap ℝ (PhaseSpace (Fin d)) ε * p i

/-- The inverse of the inertia. -/
def inertiaInv (d : ℕ) (m ε : ℝ) : PhaseSpace (Fin d) :=
  relEnergyInv m fun i => algebraMap ℝ (PhaseSpace (Fin d)) ε * p i

/-- The boost charge `Kᵢ = inertia · qᵢ` at time zero. -/
def boostCharge (d : ℕ) (m ε : ℝ) (i : Fin d) : PhaseSpace (Fin d) := inertia d m ε * q i

variable {m : ℝ}

/-- Without the speed of light the inertia is the mass. -/
theorem inertia_zero (d : ℕ) (m : ℝ) : inertia d m 0 = algebraMap ℝ (PhaseSpace (Fin d)) m := by
  rw [inertia]
  simp only [map_zero, zero_mul]
  exact relEnergy_zero m

/-- Without the speed of light the boost charge is the Galilei charge `m qᵢ`. -/
theorem boostCharge_zero (d : ℕ) (m : ℝ) (i : Fin d) :
    boostCharge d m 0 i = algebraMap ℝ (PhaseSpace (Fin d)) m * q i := by
  rw [boostCharge, inertia_zero]

/-- With `c = 1` the inertia is the energy `√(m² + Σ pᵢ²)`. -/
theorem inertia_one (d : ℕ) (m : ℝ) : inertia d m 1 = relEnergy m p := by
  rw [inertia]
  simp only [map_one, one_mul]

theorem inertia_mul_inertiaInv (hm : m ≠ 0) (ε : ℝ) : inertia d m ε * inertiaInv d m ε = 1 :=
  relEnergy_mul_relEnergyInv hm _

theorem partialDerivation_inr_inertia (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    partialDerivation (Sum.inr i) (inertia d m ε) =
      algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * (inertiaInv d m ε * p i) := by
  rw [inertia, SmoothDerivation.apply_relEnergy hm, Finset.sum_eq_single i]
  · rw [SmoothDerivation.map_algebraMap_mul, p, partialDerivation_generator_self, smul_eq_mul,
      mul_one, inertiaInv, pow_two, map_mul]
    ring
  · intro j _ hj
    rw [SmoothDerivation.map_algebraMap_mul, p,
      partialDerivation_generator_of_ne (c := Sum.inr i) (i := Sum.inr j) (by simpa using hj),
      smul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem partialDerivation_inl_inertia (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    partialDerivation (Sum.inl i) (inertia d m ε) = 0 := by
  rw [inertia, SmoothDerivation.apply_relEnergy hm, Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [SmoothDerivation.map_algebraMap_mul, p,
    partialDerivation_generator_of_ne (c := Sum.inl i) (i := Sum.inr j) (by simp), smul_zero,
    mul_zero]

/-- `{qᵢ, inertia} = ε² pᵢ / inertia`. -/
theorem canonical_q_inertia (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (q i) (inertia d m ε) =
      algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * (inertiaInv d m ε * p i) := by
  rw [canonical_q_bracket, partialDerivation_inr_inertia hm]

/-- `{pᵢ, inertia} = 0`. -/
theorem canonical_p_inertia (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (inertia d m ε) = 0 := by
  rw [canonical_p_bracket, partialDerivation_inl_inertia hm, neg_zero]

theorem canonical_inertia_p (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (inertia d m ε) (p i) = 0 := by
  rw [(canonical (Fin d)).antisymm, canonical_p_inertia hm, neg_zero]

/-- `{Kᵢ, pⱼ} = δᵢⱼ · inertia`: at `ε = 0` the mass is a central term. -/
theorem canonical_boostCharge_p (hm : m ≠ 0) (ε : ℝ) (i j : Fin d) :
    (canonical (Fin d)).bracket (boostCharge d m ε i) (p j) =
      if i = j then inertia d m ε else 0 := by
  rw [boostCharge, AlmostPoissonStructure.bracket_mul_left, canonical_q_p,
    canonical_inertia_p hm, mul_zero, add_zero]
  split_ifs <;> simp

/-- `{Kᵢ, inertia} = ε² pᵢ`: with the energy `H = inertia / ε²` this is `{Kᵢ, H} = pᵢ`. -/
theorem canonical_boostCharge_inertia (hm : m ≠ 0) (ε : ℝ) (i : Fin d) :
    (canonical (Fin d)).bracket (boostCharge d m ε i) (inertia d m ε) =
      algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * p i := by
  have h := inertia_mul_inertiaInv (d := d) hm ε
  rw [boostCharge, AlmostPoissonStructure.bracket_mul_left, canonical_q_inertia hm,
    AlmostPoissonStructure.bracket_self, mul_zero, add_zero]
  linear_combination algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * p i * h

/-- `{Kᵢ, Kⱼ} = −ε² Mᵢⱼ`: the boosts commute without the speed of light. -/
theorem canonical_boostCharge_boostCharge (hm : m ≠ 0) (ε : ℝ) (i j : Fin d) :
    (canonical (Fin d)).bracket (boostCharge d m ε i) (boostCharge d m ε j) =
      -(algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * angularMomentum d i j) := by
  have h := inertia_mul_inertiaInv (d := d) hm ε
  have hW : (canonical (Fin d)).bracket (inertia d m ε) (q j) =
      -(algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * (inertiaInv d m ε * p j)) := by
    rw [(canonical (Fin d)).antisymm, canonical_q_inertia hm]
  have hK : boostCharge d m ε j = inertia d m ε * q j := rfl
  rw [hK, AlmostPoissonStructure.bracket_mul_right, boostCharge,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_left,
    canonical_q_inertia hm, canonical_q_q, AlmostPoissonStructure.bracket_self, hW,
    angularMomentum_eq]
  linear_combination algebraMap ℝ (PhaseSpace (Fin d)) (ε ^ 2) * (q j * p i - q i * p j) * h

/-- The inertia is invariant under rotations. -/
theorem canonical_angularMomentum_inertia (hm : m ≠ 0) (ε : ℝ) (i j : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (inertia d m ε) = 0 := by
  rw [angularMomentum_eq, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_left,
    canonical_p_inertia hm, canonical_p_inertia hm, canonical_q_inertia hm,
    canonical_q_inertia hm]
  ring

/-- The boost charges transform as a vector: `{Mᵢⱼ, Kₖ} = δₖᵢ Kⱼ − δₖⱼ Kᵢ`. -/
theorem canonical_angularMomentum_boostCharge (hm : m ≠ 0) (ε : ℝ) (i j k : Fin d) :
    (canonical (Fin d)).bracket (angularMomentum d i j) (boostCharge d m ε k) =
      (if k = i then boostCharge d m ε j else 0) - if k = j then boostCharge d m ε i else 0 := by
  have hK : boostCharge d m ε k = inertia d m ε * q k := rfl
  rw [hK, AlmostPoissonStructure.bracket_mul_right, canonical_angularMomentum_q,
    canonical_angularMomentum_inertia hm, mul_zero, add_zero, boostCharge, boostCharge]
  split_ifs <;> ring

end ProjectAinos.SpecialRelativity.Poincare

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.CyclicReduction
public import ProjectAinos.SpecialRelativity.Hamiltonian
public import ProjectAinos.SpecialRelativity.PoincareAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The mass shell as a coisotropic ideal, and its reduction

The phase space of an event `x` and its momentum covector `p` is the canonical phase space on
`Fin (d + 1)`, with the time at the index `0`.

**The quadratic shell.** For a convention `σ` the function
`shellFunction σ d m = η⁻¹(p, p) − σ m²` vanishes on the mass shell. The ideal `shellIdeal σ d m`
that it generates is coisotropic, and the momenta `p_μ` and the Lorentz charges `J_μν` are in
its normalizer: their brackets with the generator are zero.

**The future sheet.** For `(−+++)` and `m ≠ 0`, with `E = √(m² + Σ pᵢ²)` the energy of the space
momenta, `shellFunction = (E − p₀)(p₀ + E)`. The future sheet is the ideal
`futureShellIdeal d m = (p₀ + E)`. Modulo this ideal `E − p₀` is invertible, so the normalizer
of the quadratic shell is contained in the normalizer of the future sheet
(`normalizer_shellIdeal_le`), and the Poincaré charges are in it.

**Reduction.** The change of variables

`Q⁰ = x⁰`, `Qᵢ = xᵢ − x⁰ pᵢ/E`, `P₀ = p₀ + E`, `Pᵢ = pᵢ`

is canonical (`isPoissonHom_toShellCoordinates`) and has the inverse `ofShellCoordinates`. In
these variables the future sheet is `P₀ = 0`, so the theorem on cyclic co-ordinates identifies
the reduced ring `N(I)/I` with the phase space of the initial data `(𝐐, 𝐏)`, as a Poisson
C-infinity ring (`reductionHom_bijective`, `isPoissonHom_reductionHom`). The class of an
element `f` of the normalizer is `initialData d m f` (`reductionHom_initialData`): the class of
`p₀` is minus the Hamiltonian of the free particle, the class of `J₀ᵢ` is the boost charge
`H qᵢ`, and the class of `Jᵢⱼ` is the angular momentum.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity.MassShell

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics SmoothGeometry

variable {d : ℕ} {m : ℝ}

/-- The phase space of an event and its momentum covector; the time is the index `0`. -/
abbrev EventSpace (d : ℕ) := PhaseSpace (Fin (d + 1))

/-! ### The quadratic shell -/

/-- The function `η⁻¹(p, p) − σ m²`, which vanishes on the mass shell. -/
def shellFunction (σ : LorentzConvention) (d : ℕ) (m : ℝ) : EventSpace d :=
  momentumQuadratic (Minkowski.metricMatrix σ d) -
    algebraMap ℝ (EventSpace d) (σ.timeSign * m ^ 2)

/-- The ideal of the mass shell. -/
def shellIdeal (σ : LorentzConvention) (d : ℕ) (m : ℝ) : Ideal (EventSpace d) :=
  Ideal.span {shellFunction σ d m}

/-- The mass shell is coisotropic. -/
theorem isCoisotropic_shellIdeal (σ : LorentzConvention) (d : ℕ) (m : ℝ) :
    (canonical (Fin (d + 1))).IsCoisotropic (shellIdeal σ d m) := by
  refine PoissonStructure.isCoisotropic_span fun a ha b hb => ?_
  rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb,
    AlmostPoissonStructure.bracket_self]
  exact zero_mem _

theorem bracket_p_shellFunction (σ : LorentzConvention) (m : ℝ) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (p μ) (shellFunction σ d m) = 0 := by
  rw [shellFunction, AlmostPoissonStructure.bracket_sub_right, canonical_p_momentumQuadratic,
    AlmostPoissonStructure.bracket_algebraMap_right, sub_zero]

theorem bracket_lorentzCharge_shellFunction (σ : LorentzConvention) (m : ℝ)
    (μ ν : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (Poincare.lorentzCharge σ d μ ν) (shellFunction σ d m) =
      0 := by
  rw [shellFunction, AlmostPoissonStructure.bracket_sub_right,
    Poincare.canonical_lorentzCharge_momentumQuadratic,
    AlmostPoissonStructure.bracket_algebraMap_right, sub_zero]

/-- The momenta are in the normalizer of the mass shell. -/
theorem p_mem_normalizer_shellIdeal (σ : LorentzConvention) (m : ℝ) (μ : Fin (d + 1)) :
    p μ ∈ (canonical (Fin (d + 1))).normalizer (shellIdeal σ d m) :=
  PoissonStructure.mem_normalizer_span fun a ha => by
    rw [Set.mem_singleton_iff.mp ha, bracket_p_shellFunction]
    exact zero_mem _

/-- The Lorentz charges are in the normalizer of the mass shell. -/
theorem lorentzCharge_mem_normalizer_shellIdeal (σ : LorentzConvention) (m : ℝ)
    (μ ν : Fin (d + 1)) :
    Poincare.lorentzCharge σ d μ ν ∈ (canonical (Fin (d + 1))).normalizer (shellIdeal σ d m) :=
  PoissonStructure.mem_normalizer_span fun a ha => by
    rw [Set.mem_singleton_iff.mp ha, bracket_lorentzCharge_shellFunction]
    exact zero_mem _

/-! ### The future sheet -/

/-- The energy `√(m² + Σ pᵢ²)` of the space momenta, on the phase space of an event. -/
def energy (d : ℕ) (m : ℝ) : EventSpace d := relEnergy m fun i : Fin d => p i.succ

/-- The inverse of the energy. -/
def energyInv (d : ℕ) (m : ℝ) : EventSpace d := relEnergyInv m fun i : Fin d => p i.succ

/-- The velocity `pᵢ/E`. -/
def velocity (d : ℕ) (m : ℝ) (i : Fin d) : EventSpace d := energyInv d m * p i.succ

/-- The function `p₀ + E`, which vanishes on the future sheet of the mass shell for `(−+++)`. -/
def futureShellFunction (d : ℕ) (m : ℝ) : EventSpace d := p 0 + energy d m

/-- The ideal of the future sheet of the mass shell. -/
def futureShellIdeal (d : ℕ) (m : ℝ) : Ideal (EventSpace d) :=
  Ideal.span {futureShellFunction d m}

theorem energy_mul_energyInv (hm : m ≠ 0) : energy d m * energyInv d m = 1 :=
  relEnergy_mul_relEnergyInv hm _

theorem energy_mul_self (hm : m ≠ 0) :
    energy d m * energy d m =
      algebraMap ℝ (EventSpace d) (m ^ 2) + ∑ i : Fin d, p i.succ * p i.succ :=
  relEnergy_mul_self hm _

theorem lorentzSign_timeNegative_zero :
    lorentzSign .timeNegative (0 : Fin (d + 1)) = -1 := by
  simp [lorentzSign]

theorem lorentzSign_timeNegative_succ (i : Fin d) :
    lorentzSign .timeNegative i.succ = 1 := by
  simp [lorentzSign]

/-- The quadratic shell function is `(E − p₀)(p₀ + E)`. -/
theorem shellFunction_eq (hm : m ≠ 0) :
    shellFunction .timeNegative d m = (energy d m - p 0) * futureShellFunction d m := by
  have h := energy_mul_self (d := d) hm
  have hneg : algebraMap ℝ (EventSpace d) (-1) = -1 := by rw [map_neg, map_one]
  rw [shellFunction, Minkowski.metricMatrix, momentumQuadratic_diagonal, Fin.sum_univ_succ,
    lorentzSign_timeNegative_zero, futureShellFunction]
  simp only [lorentzSign_timeNegative_succ, LorentzConvention.timeSign_timeNegative, map_mul,
    Algebra.smul_def, hneg, map_one, one_mul]
  linear_combination (-1 : EventSpace d) * h

theorem shellIdeal_le_futureShellIdeal (hm : m ≠ 0) :
    shellIdeal .timeNegative d m ≤ futureShellIdeal d m := by
  rw [shellIdeal, futureShellIdeal, Ideal.span_singleton_le_iff_mem, shellFunction_eq hm]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The future sheet is coisotropic. -/
theorem isCoisotropic_futureShellIdeal (d : ℕ) (m : ℝ) :
    (canonical (Fin (d + 1))).IsCoisotropic (futureShellIdeal d m) := by
  refine PoissonStructure.isCoisotropic_span fun a ha b hb => ?_
  rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb,
    AlmostPoissonStructure.bracket_self]
  exact zero_mem _

/-- The normalizer of the mass shell is contained in the normalizer of its future sheet: modulo
`p₀ + E` the other factor `E − p₀` is invertible. -/
theorem normalizer_shellIdeal_le (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).normalizer (shellIdeal .timeNegative d m) ≤
      (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m) := by
  intro f hf
  refine PoissonStructure.mem_normalizer_span fun a ha => ?_
  rw [Set.mem_singleton_iff.mp ha]
  have hE := energy_mul_energyInv (d := d) hm
  have hg : futureShellFunction d m ∈ futureShellIdeal d m := Ideal.subset_span rfl
  have hc : (canonical (Fin (d + 1))).bracket f (shellFunction .timeNegative d m) ∈
      futureShellIdeal d m :=
    shellIdeal_le_futureShellIdeal hm (hf _ (Ideal.subset_span rfl))
  rw [shellFunction_eq hm, AlmostPoissonStructure.bracket_mul_right] at hc
  have h1 : (energy d m - p 0) *
      (canonical (Fin (d + 1))).bracket f (futureShellFunction d m) ∈ futureShellIdeal d m := by
    have h := sub_mem hc (Ideal.mul_mem_right
      ((canonical (Fin (d + 1))).bracket f (energy d m - p 0)) _ hg)
    rwa [add_sub_cancel_right] at h
  have h2 : (canonical (Fin (d + 1))).bracket f (futureShellFunction d m) +
      (canonical (Fin (d + 1))).bracket f (futureShellFunction d m) =
      energyInv d m * ((energy d m - p 0) *
        (canonical (Fin (d + 1))).bracket f (futureShellFunction d m)) +
      energyInv d m * (canonical (Fin (d + 1))).bracket f (futureShellFunction d m) *
        futureShellFunction d m := by
    have hF : futureShellFunction d m = p 0 + energy d m := rfl
    rw [hF]
    linear_combination
      (-2 * (canonical (Fin (d + 1))).bracket f (p 0 + energy d m)) * hE
  have h3 := add_mem (Ideal.mul_mem_left _ (energyInv d m) h1)
    (Ideal.mul_mem_left _ (energyInv d m *
      (canonical (Fin (d + 1))).bracket f (futureShellFunction d m)) hg)
  rw [← h2] at h3
  have h4 : (canonical (Fin (d + 1))).bracket f (futureShellFunction d m) =
      (1 / 2 : ℝ) • ((canonical (Fin (d + 1))).bracket f (futureShellFunction d m) +
        (canonical (Fin (d + 1))).bracket f (futureShellFunction d m)) := by
    module
  rw [h4]
  exact Submodule.smul_of_tower_mem _ _ h3

/-- The momenta are in the normalizer of the future sheet. -/
theorem p_mem_normalizer_futureShellIdeal (hm : m ≠ 0) (μ : Fin (d + 1)) :
    p μ ∈ (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m) :=
  normalizer_shellIdeal_le hm (p_mem_normalizer_shellIdeal _ m μ)

/-- The Lorentz charges are in the normalizer of the future sheet. -/
theorem lorentzCharge_mem_normalizer_futureShellIdeal (hm : m ≠ 0) (μ ν : Fin (d + 1)) :
    Poincare.lorentzCharge .timeNegative d μ ν ∈
      (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m) :=
  normalizer_shellIdeal_le hm (lorentzCharge_mem_normalizer_shellIdeal _ m μ ν)

/-! ### Brackets of the energy and of the velocity -/

/-- A bracket with the energy in the first argument, by the chain rule. -/
theorem bracket_energy (hm : m ≠ 0) (h : EventSpace d) :
    (canonical (Fin (d + 1))).bracket (energy d m) h =
      energyInv d m * ∑ j : Fin d, p j.succ * (canonical (Fin (d + 1))).bracket (p j.succ) h :=
  SmoothDerivation.apply_relEnergy hm ((canonical (Fin (d + 1))).hamiltonian h) _

theorem bracket_energyInv (hm : m ≠ 0) (h : EventSpace d) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) h =
      -(energyInv d m * energyInv d m * energyInv d m *
        ∑ j : Fin d, p j.succ * (canonical (Fin (d + 1))).bracket (p j.succ) h) :=
  SmoothDerivation.apply_relEnergyInv hm ((canonical (Fin (d + 1))).hamiltonian h) _

theorem bracket_energy_q_zero (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energy d m) (q 0) = 0 := by
  rw [bracket_energy hm, Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [canonical_p_q]
  simp only [Fin.succ_ne_zero, ↓reduceIte, mul_zero]

theorem bracket_energyInv_q_zero (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (q 0) = 0 := by
  rw [bracket_energyInv hm, Finset.sum_eq_zero, mul_zero, neg_zero]
  intro j _
  rw [canonical_p_q]
  simp only [Fin.succ_ne_zero, ↓reduceIte, mul_zero]

theorem bracket_energy_p (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (energy d m) (p μ) = 0 := by
  rw [bracket_energy hm, Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [canonical_p_p, mul_zero]

theorem bracket_energyInv_p (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (p μ) = 0 := by
  rw [bracket_energyInv hm, Finset.sum_eq_zero, mul_zero, neg_zero]
  intro j _
  rw [canonical_p_p, mul_zero]

theorem bracket_energy_q_succ (hm : m ≠ 0) (k : Fin d) :
    (canonical (Fin (d + 1))).bracket (energy d m) (q k.succ) = -velocity d m k := by
  rw [bracket_energy hm, Finset.sum_eq_single k, velocity]
  · rw [canonical_p_q]
    simp only [↓reduceIte]
    ring
  · intro j _ hj
    rw [canonical_p_q]
    simp only [Fin.succ_inj, hj, ↓reduceIte, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem bracket_energyInv_q_succ (hm : m ≠ 0) (k : Fin d) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (q k.succ) =
      energyInv d m * energyInv d m * energyInv d m * p k.succ := by
  rw [bracket_energyInv hm, Finset.sum_eq_single k]
  · rw [canonical_p_q]
    simp only [↓reduceIte]
    ring
  · intro j _ hj
    rw [canonical_p_q]
    simp only [Fin.succ_inj, hj, ↓reduceIte, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem bracket_p_energy (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (p μ) (energy d m) = 0 := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_energy_p hm, neg_zero]

theorem bracket_p_energyInv (hm : m ≠ 0) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (p μ) (energyInv d m) = 0 := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_energyInv_p hm, neg_zero]

theorem bracket_q_zero_energy (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (q 0) (energy d m) = 0 := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_energy_q_zero hm, neg_zero]

theorem bracket_q_zero_energyInv (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (q 0) (energyInv d m) = 0 := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_energyInv_q_zero hm, neg_zero]

/-- `{xᵢ, E} = pᵢ/E`. -/
theorem bracket_q_succ_energy (hm : m ≠ 0) (k : Fin d) :
    (canonical (Fin (d + 1))).bracket (q k.succ) (energy d m) = velocity d m k := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_energy_q_succ hm]
  ring

theorem bracket_energy_energyInv (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energy d m) (energyInv d m) = 0 := by
  rw [bracket_energy hm, Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [bracket_p_energyInv hm, mul_zero]

theorem bracket_energyInv_energy (hm : m ≠ 0) :
    (canonical (Fin (d + 1))).bracket (energyInv d m) (energy d m) = 0 := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_energy_energyInv hm, neg_zero]

theorem bracket_velocity_q_zero (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (q 0) = 0 := by
  rw [velocity, AlmostPoissonStructure.bracket_mul_left, canonical_p_q,
    bracket_energyInv_q_zero hm]
  simp only [Fin.succ_ne_zero, ↓reduceIte, mul_zero, add_zero]

theorem bracket_q_zero_velocity (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (q 0) (velocity d m i) = 0 := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_velocity_q_zero hm, neg_zero]

theorem bracket_velocity_p (hm : m ≠ 0) (i : Fin d) (μ : Fin (d + 1)) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (p μ) = 0 := by
  rw [velocity, AlmostPoissonStructure.bracket_mul_left, canonical_p_p, bracket_energyInv_p hm,
    mul_zero, mul_zero, add_zero]

theorem bracket_velocity_energy (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (energy d m) = 0 := by
  rw [velocity, AlmostPoissonStructure.bracket_mul_left, bracket_p_energy hm,
    bracket_energyInv_energy hm, mul_zero, mul_zero, add_zero]

theorem bracket_velocity_energyInv (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (energyInv d m) = 0 := by
  rw [velocity, AlmostPoissonStructure.bracket_mul_left, bracket_p_energyInv hm,
    AlmostPoissonStructure.bracket_self, mul_zero, mul_zero, add_zero]

theorem bracket_velocity_velocity (hm : m ≠ 0) (i j : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (velocity d m j) = 0 := by
  have h : velocity d m j = energyInv d m * p j.succ := rfl
  rw [h, AlmostPoissonStructure.bracket_mul_right, bracket_velocity_p hm,
    bracket_velocity_energyInv hm, mul_zero, mul_zero, add_zero]

/-- `{pᵢ/E, xₖ} = pᵢ pₖ/E³ − δᵢₖ/E`: the matrix of the second derivatives of the energy, which
is symmetric. -/
theorem bracket_velocity_q_succ (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (velocity d m i) (q k.succ) =
      energyInv d m * energyInv d m * energyInv d m * p i.succ * p k.succ -
        if i = k then energyInv d m else 0 := by
  rw [velocity, AlmostPoissonStructure.bracket_mul_left, canonical_p_q,
    bracket_energyInv_q_succ hm]
  simp only [Fin.succ_inj]
  split_ifs <;> ring

theorem bracket_q_succ_velocity (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (q i.succ) (velocity d m k) =
      (if k = i then energyInv d m else 0) -
        energyInv d m * energyInv d m * energyInv d m * p k.succ * p i.succ := by
  rw [(canonical (Fin (d + 1))).antisymm, bracket_velocity_q_succ hm]
  ring

/-! ### The position at the time zero -/

/-- The position at the time zero: `Qᵢ = xᵢ − x⁰ pᵢ/E`. -/
def initialPosition (d : ℕ) (m : ℝ) (i : Fin d) : EventSpace d :=
  q i.succ - q 0 * velocity d m i

theorem bracket_initialPosition_q_zero (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (q 0) = 0 := by
  rw [initialPosition, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, canonical_q_q, canonical_q_q,
    bracket_velocity_q_zero hm]
  ring

theorem bracket_initialPosition_p_zero (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (p 0) = -velocity d m i := by
  rw [initialPosition, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, canonical_q_p, canonical_q_p,
    bracket_velocity_p hm]
  simp only [Fin.succ_ne_zero, ↓reduceIte]
  ring

theorem bracket_initialPosition_p_succ (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (p k.succ) =
      if i = k then 1 else 0 := by
  rw [initialPosition, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, canonical_q_p, canonical_q_p,
    bracket_velocity_p hm]
  simp only [Fin.succ_inj, (Fin.succ_ne_zero k).symm, ↓reduceIte]
  ring

theorem bracket_initialPosition_energy (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (energy d m) = velocity d m i := by
  rw [initialPosition, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, bracket_q_succ_energy hm, bracket_q_zero_energy hm,
    bracket_velocity_energy hm]
  ring

theorem bracket_initialPosition_velocity (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (velocity d m k) =
      (if k = i then energyInv d m else 0) -
        energyInv d m * energyInv d m * energyInv d m * p k.succ * p i.succ := by
  rw [initialPosition, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, bracket_q_succ_velocity hm,
    bracket_velocity_velocity hm, bracket_q_zero_velocity hm]
  ring

theorem bracket_initialPosition_q_succ (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (q k.succ) =
      q 0 * ((if i = k then energyInv d m else 0) -
        energyInv d m * energyInv d m * energyInv d m * p i.succ * p k.succ) := by
  rw [initialPosition, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, canonical_q_q, canonical_q_q,
    bracket_velocity_q_succ hm]
  ring

/-- The positions at the time zero commute: the second derivatives of the energy are
symmetric. -/
theorem bracket_initialPosition_initialPosition (hm : m ≠ 0) (i k : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (initialPosition d m k) = 0 := by
  have h : initialPosition d m k = q k.succ - q 0 * velocity d m k := rfl
  rw [h, AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_right,
    bracket_initialPosition_q_succ hm, bracket_initialPosition_velocity hm,
    bracket_initialPosition_q_zero hm]
  rcases eq_or_ne i k with rfl | hik
  · simp only [↓reduceIte]
    ring
  · simp only [hik, hik.symm, ↓reduceIte]
    ring

theorem bracket_initialPosition_futureShellFunction (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin (d + 1))).bracket (initialPosition d m i) (futureShellFunction d m) = 0 := by
  rw [futureShellFunction, AlmostPoissonStructure.bracket_add_right,
    bracket_initialPosition_p_zero hm, bracket_initialPosition_energy hm]
  ring

/-! ### The canonical change of variables -/

/-- The new variables as functions of the event and its momentum:
`Qᵢ = xᵢ − x⁰ pᵢ/E`, `Q⁰ = x⁰`, `Pᵢ = pᵢ`, `P₀ = p₀ + E`. -/
def shellCoordinates (d : ℕ) (m : ℝ) : (Fin d ⊕ Unit) ⊕ (Fin d ⊕ Unit) → EventSpace d :=
  Sum.elim (Sum.elim (initialPosition d m) fun _ => q 0)
    (Sum.elim (fun i => p i.succ) fun _ => futureShellFunction d m)

/-- The change of variables, as a morphism from the phase space of the new variables. -/
def toShellCoordinates (d : ℕ) (m : ℝ) :
    SmoothRingHom (PhaseSpace (Fin d ⊕ Unit)) (EventSpace d) :=
  FreeSmoothRing.lift (shellCoordinates d m)

/-- The event and its momentum as functions of the new variables. -/
def eventCoordinates (d : ℕ) (m : ℝ) :
    Fin (d + 1) ⊕ Fin (d + 1) → PhaseSpace (Fin d ⊕ Unit) :=
  Sum.elim
    (Fin.cons (q (Sum.inr ())) fun i : Fin d => q (Sum.inl i) + q (Sum.inr ()) *
      (relEnergyInv m (fun j : Fin d => p (Sum.inl j)) * p (Sum.inl i)))
    (Fin.cons (p (Sum.inr ()) - relEnergy m fun j : Fin d => p (Sum.inl j))
      fun i : Fin d => p (Sum.inl i))

/-- The inverse change of variables. -/
def ofShellCoordinates (d : ℕ) (m : ℝ) :
    SmoothRingHom (EventSpace d) (PhaseSpace (Fin d ⊕ Unit)) :=
  FreeSmoothRing.lift (eventCoordinates d m)

theorem toShellCoordinates_q_inl (m : ℝ) (i : Fin d) :
    toShellCoordinates d m (q (Sum.inl i)) = initialPosition d m i :=
  lift_generator _ _

theorem toShellCoordinates_q_inr (d : ℕ) (m : ℝ) :
    toShellCoordinates d m (q (Sum.inr ())) = q 0 :=
  lift_generator _ _

theorem toShellCoordinates_p_inl (m : ℝ) (i : Fin d) :
    toShellCoordinates d m (p (Sum.inl i)) = p i.succ :=
  lift_generator _ _

theorem toShellCoordinates_p_inr (d : ℕ) (m : ℝ) :
    toShellCoordinates d m (p (Sum.inr ())) = futureShellFunction d m :=
  lift_generator _ _

theorem ofShellCoordinates_q_zero (d : ℕ) (m : ℝ) :
    ofShellCoordinates d m (q 0) = q (Sum.inr ()) := by
  rw [ofShellCoordinates, q, lift_generator, eventCoordinates, Sum.elim_inl, Fin.cons_zero]

theorem ofShellCoordinates_q_succ (m : ℝ) (i : Fin d) :
    ofShellCoordinates d m (q i.succ) = q (Sum.inl i) + q (Sum.inr ()) *
      (relEnergyInv m (fun j : Fin d => p (Sum.inl j)) * p (Sum.inl i)) := by
  rw [ofShellCoordinates, q, lift_generator, eventCoordinates, Sum.elim_inl, Fin.cons_succ]

theorem ofShellCoordinates_p_zero (d : ℕ) (m : ℝ) :
    ofShellCoordinates d m (p 0) =
      p (Sum.inr ()) - relEnergy m fun j : Fin d => p (Sum.inl j) := by
  rw [ofShellCoordinates, p, lift_generator, eventCoordinates, Sum.elim_inr, Fin.cons_zero]

theorem ofShellCoordinates_p_succ (m : ℝ) (i : Fin d) :
    ofShellCoordinates d m (p i.succ) = p (Sum.inl i) := by
  rw [ofShellCoordinates, p, lift_generator, eventCoordinates, Sum.elim_inr, Fin.cons_succ]

/-- The two changes of variables are inverse to each other. -/
theorem toShellCoordinates_ofShellCoordinates (m : ℝ) (f : EventSpace d) :
    toShellCoordinates d m (ofShellCoordinates d m f) = f := by
  have h : (toShellCoordinates d m).comp (ofShellCoordinates d m) =
      SmoothRingHom.id (EventSpace d) := by
    refine FreeSmoothRing.hom_ext fun a => ?_
    rcases a with μ | μ
    · refine Fin.cases ?_ (fun i => ?_) μ
      · change toShellCoordinates d m (ofShellCoordinates d m (q 0)) = q 0
        rw [ofShellCoordinates_q_zero, toShellCoordinates_q_inr]
      · change toShellCoordinates d m (ofShellCoordinates d m (q i.succ)) = q i.succ
        rw [ofShellCoordinates_q_succ, SmoothRingHom.map_add, SmoothRingHom.map_mul,
          SmoothRingHom.map_mul, SmoothRingHom.map_relEnergyInv]
        simp only [toShellCoordinates_q_inl, toShellCoordinates_q_inr, toShellCoordinates_p_inl]
        rw [initialPosition, velocity, energyInv]
        ring
    · refine Fin.cases ?_ (fun i => ?_) μ
      · change toShellCoordinates d m (ofShellCoordinates d m (p 0)) = p 0
        rw [ofShellCoordinates_p_zero, SmoothRingHom.map_sub, SmoothRingHom.map_relEnergy]
        simp only [toShellCoordinates_p_inr, toShellCoordinates_p_inl]
        rw [futureShellFunction, energy]
        ring
      · change toShellCoordinates d m (ofShellCoordinates d m (p i.succ)) = p i.succ
        rw [ofShellCoordinates_p_succ, toShellCoordinates_p_inl]
  exact congrArg (fun χ : SmoothRingHom (EventSpace d) (EventSpace d) => χ f) h

theorem ofShellCoordinates_toShellCoordinates (m : ℝ) (g : PhaseSpace (Fin d ⊕ Unit)) :
    ofShellCoordinates d m (toShellCoordinates d m g) = g := by
  have h : (ofShellCoordinates d m).comp (toShellCoordinates d m) =
      SmoothRingHom.id (PhaseSpace (Fin d ⊕ Unit)) := by
    refine FreeSmoothRing.hom_ext fun a => ?_
    rcases a with (i | ⟨⟩) | (i | ⟨⟩)
    · change ofShellCoordinates d m (toShellCoordinates d m (q (Sum.inl i))) = q (Sum.inl i)
      rw [toShellCoordinates_q_inl, initialPosition, velocity, energyInv,
        SmoothRingHom.map_sub, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
        SmoothRingHom.map_relEnergyInv]
      simp only [ofShellCoordinates_q_succ, ofShellCoordinates_q_zero,
        ofShellCoordinates_p_succ]
      ring
    · change ofShellCoordinates d m (toShellCoordinates d m (q (Sum.inr ()))) = q (Sum.inr ())
      rw [toShellCoordinates_q_inr, ofShellCoordinates_q_zero]
    · change ofShellCoordinates d m (toShellCoordinates d m (p (Sum.inl i))) = p (Sum.inl i)
      rw [toShellCoordinates_p_inl, ofShellCoordinates_p_succ]
    · change ofShellCoordinates d m (toShellCoordinates d m (p (Sum.inr ()))) = p (Sum.inr ())
      rw [toShellCoordinates_p_inr, futureShellFunction, energy, SmoothRingHom.map_add,
        SmoothRingHom.map_relEnergy]
      simp only [ofShellCoordinates_p_zero, ofShellCoordinates_p_succ]
      ring
  exact congrArg
    (fun χ : SmoothRingHom (PhaseSpace (Fin d ⊕ Unit)) (PhaseSpace (Fin d ⊕ Unit)) => χ g) h

/-- The change of variables is canonical. -/
theorem isPoissonHom_toShellCoordinates (hm : m ≠ 0) :
    IsPoissonHom (canonical (Fin d ⊕ Unit)).toAlmostPoissonStructure
      (canonical (Fin (d + 1))).toAlmostPoissonStructure (toShellCoordinates d m) := by
  refine isPoissonHom_of_canonical ?_ ?_ ?_
  · rintro (i | ⟨⟩) (j | ⟨⟩)
    · rw [toShellCoordinates_q_inl, toShellCoordinates_q_inl]
      exact bracket_initialPosition_initialPosition hm i j
    · rw [toShellCoordinates_q_inl, toShellCoordinates_q_inr]
      exact bracket_initialPosition_q_zero hm i
    · rw [toShellCoordinates_q_inl, toShellCoordinates_q_inr,
        (canonical (Fin (d + 1))).antisymm, bracket_initialPosition_q_zero hm, neg_zero]
    · rw [toShellCoordinates_q_inr]
      exact canonical_q_q 0 0
  · rintro (i | ⟨⟩) (j | ⟨⟩)
    · rw [toShellCoordinates_p_inl, toShellCoordinates_p_inl]
      exact canonical_p_p _ _
    · rw [toShellCoordinates_p_inl, toShellCoordinates_p_inr, futureShellFunction,
        AlmostPoissonStructure.bracket_add_right, canonical_p_p, bracket_p_energy hm, add_zero]
    · rw [toShellCoordinates_p_inl, toShellCoordinates_p_inr, futureShellFunction,
        AlmostPoissonStructure.bracket_add_left, canonical_p_p, bracket_energy_p hm, add_zero]
    · rw [toShellCoordinates_p_inr]
      exact AlmostPoissonStructure.bracket_self _ _
  · rintro (i | ⟨⟩) (j | ⟨⟩)
    · rw [toShellCoordinates_q_inl, toShellCoordinates_p_inl,
        bracket_initialPosition_p_succ hm]
      simp only [Sum.inl.injEq]
    · rw [toShellCoordinates_q_inl, toShellCoordinates_p_inr,
        bracket_initialPosition_futureShellFunction hm]
      simp only [reduceCtorEq, ↓reduceIte]
    · rw [toShellCoordinates_q_inr, toShellCoordinates_p_inl, canonical_q_p]
      simp only [(Fin.succ_ne_zero j).symm, reduceCtorEq, ↓reduceIte]
    · rw [toShellCoordinates_q_inr, toShellCoordinates_p_inr, futureShellFunction,
        AlmostPoissonStructure.bracket_add_right, canonical_q_p, bracket_q_zero_energy hm,
        add_zero]
      simp only [↓reduceIte]

/-! ### The reduced ring -/

/-- In the new variables the future sheet is the equation `P₀ = 0`. -/
theorem futureShellIdeal_eq (d : ℕ) (m : ℝ) :
    futureShellIdeal d m = Ideal.span (Set.range fun k : Unit =>
      toShellCoordinates d m (CyclicReduction.momentumEquation (Fin d) (fun _ => 0) k)) := by
  have h (k : Unit) : toShellCoordinates d m
      (CyclicReduction.momentumEquation (Fin d) (fun _ => 0) k) = futureShellFunction d m := by
    rw [CyclicReduction.momentumEquation, SmoothRingHom.map_sub, SmoothRingHom.map_algebraMap,
      map_zero, sub_zero]
    exact toShellCoordinates_p_inr d m
  simp only [h, Set.range_const]
  rfl

/-- The morphism from the phase space of the initial data to the reduced ring of the future
sheet. -/
def reductionHom (d : ℕ) (hm : m ≠ 0) : SmoothRingHom (PhaseSpace (Fin d))
    ((canonical (Fin (d + 1))).Reduction (futureShellIdeal d m)) :=
  CyclicReduction.canonicalReductionHom (isPoissonHom_toShellCoordinates hm)
    (futureShellIdeal_eq d m)

/-- The reduced ring of the future sheet of the mass shell is the phase space of the initial
data. -/
theorem reductionHom_bijective (hm : m ≠ 0) :
    Function.Bijective (reductionHom d hm) :=
  CyclicReduction.canonicalReductionHom_bijective (isPoissonHom_toShellCoordinates hm)
    (toShellCoordinates_ofShellCoordinates m) (ofShellCoordinates_toShellCoordinates m)
    (futureShellIdeal_eq d m)

/-- The identification of the reduced ring preserves the bracket. -/
theorem isPoissonHom_reductionHom (hm : m ≠ 0) :
    IsPoissonHom (canonical (Fin d)).toAlmostPoissonStructure
      ((canonical (Fin (d + 1))).reduction (futureShellIdeal d m)).toAlmostPoissonStructure
      (reductionHom d hm) :=
  CyclicReduction.isPoissonHom_canonicalReductionHom (isPoissonHom_toShellCoordinates hm)
    (futureShellIdeal_eq d m)

/-- A function of the event and its momentum, as a function of the initial data: its value at
the time zero and on the future sheet. -/
def initialData (d : ℕ) (m : ℝ) : SmoothRingHom (EventSpace d) (PhaseSpace (Fin d)) :=
  (CyclicReduction.restriction (Fin d) fun _ : Unit => (0 : ℝ)).comp (ofShellCoordinates d m)

/-- The class of an element of the normalizer is its function of the initial data. -/
theorem reductionHom_initialData (hm : m ≠ 0) {f : EventSpace d}
    (hf : f ∈ (canonical (Fin (d + 1))).normalizer (futureShellIdeal d m)) :
    reductionHom d hm (initialData d m f) =
      (canonical (Fin (d + 1))).reductionMap (futureShellIdeal d m) ⟨f, hf⟩ :=
  CyclicReduction.canonicalReductionHom_restriction (isPoissonHom_toShellCoordinates hm)
    (toShellCoordinates_ofShellCoordinates m) (ofShellCoordinates_toShellCoordinates m)
    (futureShellIdeal_eq d m) hf

theorem initialData_q_zero (d : ℕ) (m : ℝ) : initialData d m (q 0) = 0 := by
  rw [initialData, SmoothRingHom.comp_apply, ofShellCoordinates_q_zero, q,
    CyclicReduction.restriction, lift_generator]
  rfl

theorem initialData_p_succ (m : ℝ) (i : Fin d) : initialData d m (p i.succ) = p i := by
  rw [initialData, SmoothRingHom.comp_apply, ofShellCoordinates_p_succ, p,
    CyclicReduction.restriction, lift_generator]
  rfl

/-- The class of `p₀` is minus the Hamiltonian of the free particle. -/
theorem initialData_p_zero (d : ℕ) (m : ℝ) :
    initialData d m (p 0) = -FreeParticle.hamiltonian d m := by
  rw [initialData, SmoothRingHom.comp_apply, ofShellCoordinates_p_zero, SmoothRingHom.map_sub,
    SmoothRingHom.map_relEnergy, p, CyclicReduction.restriction, lift_generator]
  simp only [p, lift_generator, Sum.elim_inr, Sum.elim_inl, map_zero, zero_sub]
  rfl

theorem initialData_q_succ (m : ℝ) (i : Fin d) : initialData d m (q i.succ) = q i := by
  rw [initialData, SmoothRingHom.comp_apply, ofShellCoordinates_q_succ, SmoothRingHom.map_add,
    SmoothRingHom.map_mul, q, q, CyclicReduction.restriction, lift_generator, lift_generator]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, add_zero]

/-- The class of `J₀ᵢ` is the boost charge `H qᵢ` at the time zero. -/
theorem initialData_lorentzCharge_zero_succ (m : ℝ) (i : Fin d) :
    initialData d m (Poincare.lorentzCharge .timeNegative d 0 i.succ) =
      FreeParticle.hamiltonian d m * q i := by
  rw [Poincare.lorentzCharge_eq, lorentzSign_timeNegative_zero, lorentzSign_timeNegative_succ,
    one_smul, Algebra.smul_def, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
    SmoothRingHom.map_mul, SmoothRingHom.map_mul, initialData_q_zero, initialData_p_succ,
    initialData_q_succ, initialData_p_zero]
  ring

/-- The class of `Jᵢⱼ` is the angular momentum. -/
theorem initialData_lorentzCharge_succ_succ (m : ℝ) (i j : Fin d) :
    initialData d m (Poincare.lorentzCharge .timeNegative d i.succ j.succ) =
      Poincare.angularMomentum d i j := by
  rw [Poincare.lorentzCharge_eq, lorentzSign_timeNegative_succ, lorentzSign_timeNegative_succ,
    one_smul, one_smul, SmoothRingHom.map_sub, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
    initialData_q_succ, initialData_p_succ, initialData_q_succ, initialData_p_succ,
    Poincare.angularMomentum_eq]

end ProjectAinos.SpecialRelativity.MassShell

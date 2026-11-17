/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.MassShellReduction
public import ProjectAinos.SpecialRelativity.SpatialLegendre
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The future mass shell as a graph over the space momenta

For a mass `m ≥ 0` the future mass shell is the set `FutureShell.shell d m` of the momentum
vectors with `Q(p) = m²` and a positive time component (Landau–Lifshitz, *The Classical Theory of
Fields*, §9). It is the graph of the energy `√(m² + Σ πᵢ²)` over the space momenta `π`:

* `domain d m` is the open set `0 < m² + Σ πᵢ²` of the space momenta: all of them for `m ≠ 0`
  (`domain_eq_univ`), and the nonzero ones for `m = 0` (`mem_domain_zero`);
* `point m π` is the point of the shell over `π` and `spaceMomentum p` is the space part of `p`;
  `chart d m` is the bijection between the domain and the shell, `point` is smooth on the domain
  (`contDiffOn_point`), and `spaceMomentum` is linear. The shell is in this way the open set
  `domainOpens d m` of the space momenta, and `scheme d m` is its C-infinity scheme;
* the massless shell is the future light cone without its vertex (`mem_shell_zero_iff`), and
  the vertex is in no shell (`zero_notMem_shell`).

**The Lorentz group.** An orthochronous Lorentz transformation maps the shell to itself
(`lorentz_mem_shell`). In the chart it is `action m L π`, which maps the domain to itself, is
smooth there (`contDiffOn_action`), and satisfies the laws of an action (`action_one`,
`action_mul`).

**The ideal of the shell.** For `m > 0`, a real point of the phase space of an event is a zero
of the function `p₀ + E` of the future sheet if and only if its momentum vector is on the shell
(`lift_futureShellFunction_eq_zero_iff`).
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.SpecialRelativity.FutureShell

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace
open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {m : ℝ}

/-- The future mass shell: the momentum vectors with `Q(p) = m²` and a positive energy. -/
def shell (d : ℕ) (m : ℝ) : Set (MinkowskiModel d) :=
  {p | intervalQuadratic p = m ^ 2 ∧ 0 < time p}

/-- The space momenta over which the shell is a graph. -/
def domain (d : ℕ) (m : ℝ) : Set (Fin d → ℝ) := {π | 0 < m ^ 2 + ∑ i, π i ^ 2}

/-- The energy `√(m² + Σ πᵢ²)` on the shell. -/
def energy (m : ℝ) (π : Fin d → ℝ) : ℝ := Real.sqrt (m ^ 2 + ∑ i, π i ^ 2)

/-- The point of the shell over the space momentum `π`. -/
def point (m : ℝ) (π : Fin d → ℝ) : MinkowskiModel d := Fin.cons (energy m π) π

/-- The space momentum of a momentum vector, in co-ordinates. -/
def spaceMomentum (p : MinkowskiModel d) : Fin d → ℝ := fun i => p i.succ

/-! ### The domain -/

theorem isOpen_domain : IsOpen (domain d m) :=
  isOpen_lt continuous_const
    (continuous_const.add (FreeParticle.contDiff_sum_sq (n := 0)).continuous)

theorem domain_eq_univ (hm : m ≠ 0) : domain d m = univ := by
  refine eq_univ_of_forall fun π => ?_
  have h1 : 0 < m ^ 2 := by positivity
  have h2 : 0 ≤ ∑ i, π i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (π i)
  exact add_pos_of_pos_of_nonneg h1 h2

theorem mem_domain_zero (π : Fin d → ℝ) : π ∈ domain d 0 ↔ π ≠ 0 := by
  have h2 : 0 ≤ ∑ i, π i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (π i)
  constructor
  · rintro h rfl
    have h' : (0 : ℝ) < (0 : ℝ) ^ 2 + ∑ i : Fin d, (0 : Fin d → ℝ) i ^ 2 := h
    simp at h'
  · intro hne
    change 0 < (0 : ℝ) ^ 2 + ∑ i, π i ^ 2
    rw [zero_pow two_ne_zero, zero_add]
    refine lt_of_le_of_ne h2 fun h0 => hne ?_
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (π j)).mp h0.symm i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff two_ne_zero |>.mp hi

/-! ### The graph -/

theorem spaceMomentum_point (m : ℝ) (π : Fin d → ℝ) : spaceMomentum (point m π) = π := rfl

theorem time_point (m : ℝ) (π : Fin d → ℝ) : time (point m π) = energy m π := rfl

theorem cons_time_spaceMomentum (p : MinkowskiModel d) :
    (Fin.cons (time p) (spaceMomentum p) : MinkowskiModel d) = p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The quadratic form in the time and the space momentum: `Q(p) = (p⁰)² − Σ πᵢ²`. -/
theorem intervalQuadratic_eq (p : MinkowskiModel d) :
    intervalQuadratic p = time p ^ 2 - ∑ i, spaceMomentum p i ^ 2 := by
  conv_lhs => rw [← cons_time_spaceMomentum p]
  exact FreeParticle.intervalQuadratic_cons _ _

theorem energy_sq {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    energy m π ^ 2 = m ^ 2 + ∑ i, π i ^ 2 :=
  Real.sq_sqrt (le_of_lt hπ)

theorem energy_pos {π : Fin d → ℝ} (hπ : π ∈ domain d m) : 0 < energy m π :=
  Real.sqrt_pos.mpr hπ

/-- The point over a space momentum of the domain is on the shell. -/
theorem point_mem {π : Fin d → ℝ} (hπ : π ∈ domain d m) : point m π ∈ shell d m := by
  refine ⟨?_, energy_pos hπ⟩
  rw [intervalQuadratic_eq, time_point, spaceMomentum_point, energy_sq hπ]
  ring

/-- The space momentum of a point of the shell is in the domain. -/
theorem spaceMomentum_mem {p : MinkowskiModel d} (hp : p ∈ shell d m) :
    spaceMomentum p ∈ domain d m := by
  have hQ := hp.1
  rw [intervalQuadratic_eq] at hQ
  change 0 < m ^ 2 + ∑ i, spaceMomentum p i ^ 2
  have ht : 0 < time p ^ 2 := pow_pos hp.2 2
  linarith

/-- A point of the shell is the point over its space momentum. -/
theorem point_spaceMomentum {p : MinkowskiModel d} (hp : p ∈ shell d m) :
    point m (spaceMomentum p) = p := by
  have hQ := hp.1
  rw [intervalQuadratic_eq] at hQ
  have hE : energy m (spaceMomentum p) = time p := by
    rw [energy, show m ^ 2 + ∑ i, spaceMomentum p i ^ 2 = time p ^ 2 by linarith,
      Real.sqrt_sq hp.2.le]
  rw [point, hE]
  exact cons_time_spaceMomentum p

/-- The chart of the shell: the bijection between the domain of the space momenta and the
shell. -/
def chart (d : ℕ) (m : ℝ) : domain d m ≃ shell d m where
  toFun π := ⟨point m π, point_mem π.2⟩
  invFun p := ⟨spaceMomentum p, spaceMomentum_mem p.2⟩
  left_inv π := Subtype.ext (spaceMomentum_point m π.1)
  right_inv p := Subtype.ext (point_spaceMomentum p.2)

theorem contDiffOn_energy : ContDiffOn ℝ ∞ (energy (d := d) m) (domain d m) := by
  intro π hπ
  have hsum : ContDiffAt ℝ ∞ (fun π : Fin d → ℝ => m ^ 2 + ∑ i, π i ^ 2) π :=
    (contDiff_const.add FreeParticle.contDiff_sum_sq).contDiffAt
  exact (hsum.sqrt (ne_of_gt hπ)).contDiffWithinAt

/-- The graph is smooth on the domain. -/
theorem contDiffOn_point : ContDiffOn ℝ ∞ (point (d := d) m) (domain d m) := by
  rw [contDiffOn_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contDiffOn_energy
  · exact (contDiff_apply ℝ (fun _ : Fin d => ℝ) j).contDiffOn

theorem contDiff_spaceMomentum : ContDiff ℝ ∞ (spaceMomentum (d := d)) :=
  contDiff_pi.mpr fun i => contDiff_apply ℝ (fun _ : Fin (d + 1) => ℝ) i.succ

/-- A point of the shell is in the closed future cone. -/
theorem futureCausal_of_mem {p : MinkowskiModel d} (hp : p ∈ shell d m) : FutureCausal p :=
  (futureCausal_iff p).mpr ⟨by change 0 ≤ intervalQuadratic p; rw [hp.1]; exact sq_nonneg m,
    hp.2.le⟩

/-- The vertex of the cone is in no shell. -/
theorem zero_notMem_shell : (0 : MinkowskiModel d) ∉ shell d m := by
  intro h
  have h2 := h.2
  rw [map_zero] at h2
  exact lt_irrefl _ h2

/-- The massless shell is the future light cone without its vertex. -/
theorem mem_shell_zero_iff (p : MinkowskiModel d) :
    p ∈ shell d 0 ↔ Lightlike p ∧ FutureCausal p := by
  constructor
  · intro h
    have hQ : intervalQuadratic p = 0 := by rw [h.1]; ring
    refine ⟨⟨fun h0 => zero_notMem_shell (h0 ▸ h), hQ⟩, futureCausal_of_mem h⟩
  · rintro ⟨⟨hne, hQ⟩, hfc⟩
    exact ⟨by rw [hQ]; ring, time_pos_of_futureCausal_ne_zero hfc hne⟩

/-- The domain of the space momenta, as an open set. -/
def domainOpens (d : ℕ) (m : ℝ) : TopologicalSpace.Opens (Fin d → ℝ) :=
  ⟨domain d m, isOpen_domain⟩

/-- The C-infinity scheme of the shell: the scheme of the open set of its chart. -/
def scheme (d : ℕ) (m : ℝ) : SmoothGeometry.Scheme :=
  SmoothGeometry.Manifold.scheme d (domainOpens d m)

/-! ### The action of the Lorentz group -/

/-- An orthochronous Lorentz transformation maps the shell to itself. -/
theorem lorentz_mem_shell (L : orthochronousLorentzGroup d) {p : MinkowskiModel d}
    (hp : p ∈ shell d m) : L.val.val p ∈ shell d m := by
  refine ⟨(LorentzGroup.preserves_interval L.val p).trans hp.1, ?_⟩
  have hfc : FutureCausal (L.val.val p) := (L.property p).mpr (futureCausal_of_mem hp)
  have hne : L.val.val p ≠ 0 := by
    intro h0
    have hp0 : p = 0 := L.val.val.injective (h0.trans (map_zero _).symm)
    exact zero_notMem_shell (d := d) (m := m) (hp0 ▸ hp)
  exact time_pos_of_futureCausal_ne_zero hfc hne

/-- The Lorentz transformation `L` in the chart of the shell. -/
def action (m : ℝ) (L : orthochronousLorentzGroup d) (π : Fin d → ℝ) : Fin d → ℝ :=
  spaceMomentum (L.val.val (point m π))

/-- The point over the transformed space momentum is the transformed point. -/
theorem point_action (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : point m (action m L π) = L.val.val (point m π) :=
  point_spaceMomentum (lorentz_mem_shell L (point_mem hπ))

theorem action_mem (L : orthochronousLorentzGroup d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    action m L π ∈ domain d m :=
  spaceMomentum_mem (lorentz_mem_shell L (point_mem hπ))

theorem action_one (m : ℝ) (π : Fin d → ℝ) : action m (1 : orthochronousLorentzGroup d) π = π :=
  spaceMomentum_point m π

theorem action_mul (L K : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : action m (L * K) π = action m L (action m K π) := by
  rw [action, action, point_action K hπ]
  rfl

/-- The Lorentz group acts smoothly in the chart of the shell. -/
theorem contDiffOn_action (L : orthochronousLorentzGroup d) :
    ContDiffOn ℝ ∞ (action m L) (domain d m) :=
  (contDiff_spaceMomentum.comp
    (LorentzGroup.toContinuousLinearEquiv L.val).contDiff).comp_contDiffOn contDiffOn_point

/-! ### The zeros of the function of the future sheet -/

/-- The momentum vector of a point of the phase space of an event, for `(−+++)`:
`p⁰ = −p₀` and `pⁱ = pᵢ`. -/
def momentumVector (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) : MinkowskiModel d :=
  fun μ => lorentzSign .timeNegative μ * z (Sum.inr μ)

theorem time_momentumVector (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    time (momentumVector z) = -z (Sum.inr 0) := by
  change lorentzSign .timeNegative (0 : Fin (d + 1)) * z (Sum.inr 0) = _
  rw [MassShell.lorentzSign_timeNegative_zero]
  ring

theorem spaceMomentum_momentumVector (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    spaceMomentum (momentumVector z) = fun i : Fin d => z (Sum.inr i.succ) := by
  funext i
  change lorentzSign .timeNegative i.succ * z (Sum.inr i.succ) = _
  rw [MassShell.lorentzSign_timeNegative_succ, one_mul]

/-- The value of the function of the future sheet at a point. -/
theorem lift_futureShellFunction (m : ℝ) (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    FreeSmoothRing.lift z (MassShell.futureShellFunction d m) =
      z (Sum.inr 0) + relEnergy m fun i : Fin d => z (Sum.inr i.succ) := by
  rw [MassShell.futureShellFunction, MassShell.energy, SmoothRingHom.map_add,
    SmoothRingHom.map_relEnergy]
  simp only [p, lift_generator]

/-- For a positive mass a real point of the phase space of an event is a zero of the function
of the future sheet if and only if its momentum vector is on the future mass shell. -/
theorem lift_futureShellFunction_eq_zero_iff (hm : 0 < m)
    (z : Fin (d + 1) ⊕ Fin (d + 1) → ℝ) :
    FreeSmoothRing.lift z (MassShell.futureShellFunction d m) = 0 ↔
      momentumVector z ∈ shell d m := by
  rw [lift_futureShellFunction, relEnergy_real hm]
  have hnn : 0 ≤ m ^ 2 + ∑ i : Fin d, z (Sum.inr i.succ) ^ 2 :=
    add_nonneg (sq_nonneg m) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hpos : 0 < m ^ 2 + ∑ i : Fin d, z (Sum.inr i.succ) ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hm 2) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  constructor
  · intro h
    have hE : -z (Sum.inr 0) = Real.sqrt (m ^ 2 + ∑ i : Fin d, z (Sum.inr i.succ) ^ 2) := by
      linarith
    refine ⟨?_, ?_⟩
    · rw [intervalQuadratic_eq, time_momentumVector, spaceMomentum_momentumVector, hE,
        Real.sq_sqrt hnn]
      ring
    · rw [time_momentumVector, hE]
      exact Real.sqrt_pos.mpr hpos
  · rintro ⟨hQ, ht⟩
    rw [intervalQuadratic_eq, time_momentumVector, spaceMomentum_momentumVector] at hQ
    rw [time_momentumVector] at ht
    have hsq : m ^ 2 + ∑ i : Fin d, z (Sum.inr i.succ) ^ 2 = (-z (Sum.inr 0)) ^ 2 := by linarith
    rw [hsq, Real.sqrt_sq ht.le]
    ring

end ProjectAinos.SpecialRelativity.FutureShell

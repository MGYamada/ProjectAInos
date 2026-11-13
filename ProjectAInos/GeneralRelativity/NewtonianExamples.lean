/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianBounds

/-! # A nonstatic Newtonian family with all correction types present

Compactness supplies finite C² bounds for the explicit polynomial data.
The resulting family has time-dependent potential, time correction, mixed
coefficients and spatial correction; none is removed from the scaling class.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open ContinuousLinearMap Set TopologicalSpace Metric
open scoped ContDiff Topology

namespace ProjectAInos.GeneralRelativity.NewtonianExamples
open NewtonianMetricFamily

local notation "E" => NewtonianCoordinates

/-- A common open physical-coordinate domain with a compact closure. -/
def domain : Opens E := ⟨ball 0 2, isOpen_ball⟩

def potential (q : E) : ℝ := q 0 * q 1
def timeCorrection (q : E) : ℝ := (q 0) ^ 2
def mixedCorrection (q : E) : NewtonianSpace := fun i => q 0 * q i.succ
def spatialCorrection (q : E) : NewtonianSpatialMatrix := fun i j =>
  if i = j then q 0 else 0

theorem exists_family : ∃ f : NewtonianMetricFamily domain,
    f.potential = potential ∧ f.timeCorrection = (fun _ => timeCorrection) ∧
      f.mixedCorrection = (fun _ => mixedCorrection) ∧
      f.spatialCorrection = (fun _ => spatialCorrection) := by
  have hp : ContDiff ℝ ∞ potential := by unfold potential; fun_prop
  have ha : ContDiff ℝ ∞ timeCorrection := by unfold timeCorrection; fun_prop
  have hb : ContDiff ℝ ∞ mixedCorrection := by unfold mixedCorrection; fun_prop
  have hh : ContDiff ℝ ∞ spatialCorrection := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    by_cases hij : i = j <;> simp only [spatialCorrection, hij, ite_true, ite_false] <;> fun_prop
  have hdom : (domain : Set E) ⊆ closedBall 0 2 := ball_subset_closedBall
  obtain ⟨Kp, hKp, hbp⟩ := exists_coordinateC2Bound (hp.of_le (by simp)) (isCompact_closedBall 0 2) hdom
  obtain ⟨Ka, hKa, hba⟩ := exists_coordinateC2Bound (ha.of_le (by simp)) (isCompact_closedBall 0 2) hdom
  obtain ⟨Kb, hKb, hbb⟩ := exists_coordinateC2Bound (hb.of_le (by simp)) (isCompact_closedBall 0 2) hdom
  obtain ⟨Kh, hKh, hbh⟩ := exists_coordinateC2Bound (hh.of_le (by simp)) (isCompact_closedBall 0 2) hdom
  refine ⟨{
    potential := potential
    timeCorrection := fun _ => timeCorrection
    mixedCorrection := fun _ => mixedCorrection
    spatialCorrection := fun _ => spatialCorrection
    potential_smooth := hp.contDiffOn
    time_smooth := fun _ _ => ha.contDiffOn
    mixed_smooth := fun _ _ => hb.contDiffOn
    spatial_smooth := fun _ _ => hh.contDiffOn
    spatial_symmetric := fun _ _ _ _ i j => by simp [spatialCorrection, eq_comm]
    bound := Kp + Ka + Kb + Kh
    bound_nonneg := by positivity
    potential_bound := hbp.mono (Subset.refl _) (by linarith)
    time_bound := fun _ _ => hba.mono (Subset.refl _) (by linarith)
    mixed_bound := fun _ _ => hbb.mono (Subset.refl _) (by linarith)
    spatial_bound := fun _ _ => hbh.mono (Subset.refl _) (by linarith)
  }, rfl, rfl, rfl, rfl⟩

/-- Explicit polynomial data with a proved uniform C² contract. -/
def family : NewtonianMetricFamily domain := Classical.choose exists_family

@[simp] theorem family_potential : family.potential = potential :=
  (Classical.choose_spec exists_family).1
@[simp] theorem family_timeCorrection : family.timeCorrection = (fun _ => timeCorrection) :=
  (Classical.choose_spec exists_family).2.1
@[simp] theorem family_mixedCorrection : family.mixedCorrection = (fun _ => mixedCorrection) :=
  (Classical.choose_spec exists_family).2.2.1
@[simp] theorem family_spatialCorrection : family.spatialCorrection = (fun _ => spatialCorrection) :=
  (Classical.choose_spec exists_family).2.2.2

def sample : E := ![1 / 2, 1 / 2, 0, 0]

theorem sample_mem : sample ∈ domain := by
  change dist sample 0 < 2
  rw [dist_zero_right]
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 2)).mpr
  intro i
  fin_cases i <;> norm_num [sample]

/-- At this point both mixed and spatial corrections are nonzero for positive `c`. -/
theorem sample_coefficients (c : ℝ) :
    family.coefficient c sample 0 0 = -c ^ 2 - 1 / 2 + epsilon c / 4 ∧
    family.coefficient c sample 0 1 = epsilon c / 4 ∧
    family.coefficient c sample 1 1 = 1 + epsilon c / 2 := by
  norm_num [coefficient, family_potential, family_timeCorrection, family_mixedCorrection,
    family_spatialCorrection, potential, timeCorrection, mixedCorrection, spatialCorrection, sample]
  constructor <;> ring

/-- The potential is genuinely time dependent at a point of the common domain. -/
theorem potential_time_derivative :
    fderiv ℝ family.potential sample (Pi.single 0 1) = 1 / 2 := by
  rw [family_potential]
  have hp := (proj 0 : E →L[ℝ] ℝ).hasFDerivAt (x := sample) |>.mul
    (proj 1 : E →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt potential _ sample at hp
  rw [hp.fderiv]
  norm_num [sample, Pi.single_apply]

/-- One tail works on the whole domain and every prescribed bounded velocity range. -/
theorem eventually_timelike {V : ℝ} (hV : 0 ≤ V) :
    ∀ᶠ c in Filter.atTop, ∀ q ∈ domain, ∀ v : NewtonianSpace, ‖v‖ ≤ V →
      family.form c q (timeVelocity v) (timeVelocity v) < 0 :=
  family.eventually_form_timeVelocity_neg hV

end ProjectAInos.GeneralRelativity.NewtonianExamples

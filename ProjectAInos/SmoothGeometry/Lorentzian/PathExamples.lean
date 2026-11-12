/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.MotionExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.PiecewisePath

/-! # Parallel transport along Minkowski broken lines -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry

variable {d : ℕ}
local notation "E" => MinkowskiModel d

namespace RegularPath

/-- The affine segment joining two model points. -/
def modelLine (p q : E) : RegularPath d E p q where
  curve t := (1 - t) • p + t • q
  source := by simp
  target := by simp
  regular t _ := by
    apply ContDiffAt.contMDiffAt
    fun_prop

theorem modelLine_contDiff (p q : E) : ContDiff ℝ ∞ (modelLine p q).curve := by
  change ContDiff ℝ ∞ (fun t : ℝ => (1 - t) • p + t • q)
  fun_prop

private theorem tangentCongr_modelField {p q : E} (h : p = q) (v : E) :
    tangentCongr h (LorentzMetric.modelField v p) = LorentzMetric.modelField v q := by
  subst q
  rfl

/-- Minkowski transport along a line preserves all model components, for
either signature. Endpoint equalities use native tangent-fibre casts. -/
theorem modelLine_transport (σ : LorentzConvention) (p q v : E) :
    (modelLine p q).transport (minkowskiMetric σ d) (LorentzMetric.modelField v p) =
      LorentzMetric.modelField v q := by
  let V : LorentzMetric.AlongField (d := d) (modelLine p q).curve :=
    fun t => LorentzMetric.modelField v ((modelLine p q).curve t)
  have hV : (minkowskiMetric σ d).IsParallelOn (Icc (0 : ℝ) 1) V := by
    intro t _
    refine ⟨(LorentzMetric.modelAlong_contMDiffAt (modelLine_contDiff p q).contDiffAt
      (contDiffAt_const (c := v))).mdifferentiableAt (by simp), ?_⟩
    change (minkowskiMetric σ d).covariantAlong
      (fun t => LorentzMetric.modelField v ((modelLine p q).curve t)) t = 0
    rw [LorentzMetric.minkowski_covariantAlong, deriv_const]
    exact map_zero _
  have h := (modelLine p q).transport_apply_eq (minkowskiMetric σ d) hV
  simpa only [V, tangentCongr_modelField] using h

end RegularPath

/-- Concatenated Minkowski segments preserve components without any
assumption that the two directions agree at their common endpoint. -/
theorem minkowski_brokenLine_transport (σ : LorentzConvention) (p q r v : E) :
    ((PiecewisePath.segment (RegularPath.modelLine p q)).trans
      (.segment (RegularPath.modelLine q r))).transport (minkowskiMetric σ d)
        (LorentzMetric.modelField v p) = LorentzMetric.modelField v r := by
  change (RegularPath.modelLine q r).transport (minkowskiMetric σ d)
    ((RegularPath.modelLine p q).transport (minkowskiMetric σ d) (LorentzMetric.modelField v p)) = _
  rw [RegularPath.modelLine_transport, RegularPath.modelLine_transport]

/-- A genuine corner: first move along the time axis, then the space axis. -/
theorem minkowski_corner_transport (v : MinkowskiModel 1) :
    ((PiecewisePath.segment (RegularPath.modelLine (0 : MinkowskiModel 1) ![1, 0])).trans
      (.segment (RegularPath.modelLine ![1, 0] ![1, 1]))).transport
        (minkowskiMetric .timeNegative 1) (LorentzMetric.modelField v 0) =
          LorentzMetric.modelField v ![1, 1] :=
  minkowski_brokenLine_transport .timeNegative 0 ![1, 0] ![1, 1] v

end ProjectAInos.SmoothGeometry

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.RegularPath

/-! # Parallel transport on concatenated piecewise regular paths

Finite concatenations retain their regular segments and their actual
continuous `Path`. Parallel lifts are defined independently by native
parallel fields on the segments with matching endpoint values. Their
existence and characterization justify the composed transport map even
when the velocity has a corner at a junction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry

/-- A finite piecewise `C²` path, including its chosen decomposition.
Concatenation uses the usual half-interval parametrization of `Path.trans`.
It does not require matching velocities at the junction. -/
inductive PiecewisePath (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] : M → M → Type
  | refl (x : M) : PiecewisePath d M x x
  | segment {x y : M} (p : RegularPath d M x y) : PiecewisePath d M x y
  | trans {x y z : M} (p : PiecewisePath d M x y) (q : PiecewisePath d M y z) :
      PiecewisePath d M x z

namespace PiecewisePath

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace I (M := M)

/-- The actual continuous path associated with the finite decomposition. -/
def toPath : {x y : M} → PiecewisePath d M x y → Path x y
  | _, _, .refl x => Path.refl x
  | _, _, .segment p => p.toPath
  | _, _, .trans p q => p.toPath.trans q.toPath

/-- Reverse all segments and their order. -/
def reverse : {x y : M} → PiecewisePath d M x y → PiecewisePath d M y x
  | _, _, .refl x => .refl x
  | _, _, .segment p => .segment p.reverse
  | _, _, .trans p q => .trans q.reverse p.reverse

theorem toPath_reverse {x y : M} (p : PiecewisePath d M x y) :
    p.reverse.toPath = p.toPath.symm := by
  induction p with
  | refl x => exact (Path.refl_symm).symm
  | segment p => exact p.toPath_reverse
  | trans p q hp hq => simpa only [reverse, toPath, hp, hq] using (Path.trans_symm p.toPath q.toPath).symm

/-- Compose native segment transports with the canonical endpoint identifications. -/
def transport (g : LorentzMetric σ d M) : {x y : M} → PiecewisePath d M x y → TM x ≃L[ℝ] TM y
  | _, _, .refl x => ContinuousLinearEquiv.refl ℝ (TM x)
  | _, _, .segment p => p.transport g
  | _, _, .trans p q => (transport g p).trans (transport g q)

/-- Segmentwise parallel fields with matching junction values. This
predicate does not refer to the transport map. -/
def HasParallelLift (g : LorentzMetric σ d M) :
    {x y : M} → PiecewisePath d M x y → TM x → TM y → Prop
  | _, _, .refl _, v, w => v = w
  | _, _, .segment p, v, w =>
      ∃ V : LorentzMetric.AlongField (d := d) p.curve,
        g.IsParallelOn (Icc (0 : ℝ) 1) V ∧
          tangentCongr p.source (V 0) = v ∧ tangentCongr p.target (V 1) = w
  | _, _, .trans p q, v, w => ∃ u, HasParallelLift g p v u ∧ HasParallelLift g q u w

/-- A concatenated path has a segmentwise parallel lift precisely when
its endpoint is the composed transport of its initial vector. -/
theorem hasParallelLift_iff (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) (v : TM x) (w : TM y) :
    p.HasParallelLift g v w ↔ p.transport g v = w := by
  induction p with
  | refl x => rfl
  | segment p =>
    constructor
    · rintro ⟨V, hV, hs, ht⟩
      change p.transport g v = w
      rw [← hs, p.transport_apply_eq g hV, ht]
    · intro h
      obtain ⟨V, hV, hs, ht⟩ := p.exists_parallel g v
      exact ⟨V, hV, hs, ht.trans h⟩
  | @trans x y z p q hp hq =>
    constructor
    · rintro ⟨u, hpu, hqu⟩
      change q.transport g (p.transport g v) = w
      rw [(hp v u).mp hpu]
      exact (hq u w).mp hqu
    · intro h
      exact ⟨p.transport g v, (hp v _).mpr rfl, (hq _ w).mpr h⟩

/-- Existence and uniqueness of the endpoint of a parallel lift through
any finite concatenation, including corners. -/
theorem existsUnique_parallelLift (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) (v : TM x) : ∃! w, p.HasParallelLift g v w := by
  refine ⟨p.transport g v, (p.hasParallelLift_iff g v _).mpr rfl, ?_⟩
  intro w hw
  exact ((p.hasParallelLift_iff g v w).mp hw).symm

/-- Compatibility with independently defined segmentwise parallel lifts
uniquely determines the transport map. -/
theorem transport_unique (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) (T : TM x → TM y)
    (hT : ∀ v w, p.HasParallelLift g v w → T v = w) : T = p.transport g := by
  funext v
  exact hT v _ ((p.hasParallelLift_iff g v _).mpr rfl)

/-- Matching segmentwise parallel fields concatenate to a continuous
path in the actual tangent bundle, projecting to the original path. -/
theorem exists_continuous_parallelLift (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) {v : TM x} {w : TM y} (h : p.HasParallelLift g v w) :
    ∃ P : Path (TotalSpace.mk' E x v) (TotalSpace.mk' E y w),
      P.map (FiberBundle.continuous_proj E TM) = p.toPath := by
  induction p with
  | refl x =>
    change v = w at h
    subst w
    exact ⟨Path.refl _, rfl⟩
  | segment p =>
    obtain ⟨V, hV, hs, ht⟩ := h
    let P := (p.parallelPath g hV).cast
      (by rw [hs]) (by rw [ht])
    refine ⟨P, ?_⟩
    ext t
    rfl
  | @trans x y z p q hp hq =>
    obtain ⟨u, hpu, hqu⟩ := h
    obtain ⟨P, hP⟩ := hp hpu
    obtain ⟨Q, hQ⟩ := hq hqu
    exact ⟨P.trans Q, by rw [Path.map_trans, hP, hQ]; rfl⟩

/-- Transport through a junction is composition, justified by the
independent parallel-lift characterization. -/
theorem transport_trans (g : LorentzMetric σ d M) {x y z : M}
    (p : PiecewisePath d M x y) (q : PiecewisePath d M y z) :
    (p.trans q).transport g = (p.transport g).trans (q.transport g) := rfl

/-- Grouping the pieces differently does not change endpoint transport. -/
theorem transport_assoc (g : LorentzMetric σ d M) {x y z w : M}
    (p : PiecewisePath d M x y) (q : PiecewisePath d M y z) (r : PiecewisePath d M z w) :
    ((p.trans q).trans r).transport g = (p.trans (q.trans r)).transport g := by
  ext v
  rfl

theorem transport_metric (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) (v w : TM x) :
    g.form y (p.transport g v) (p.transport g w) = g.form x v w := by
  induction p with
  | refl x => rfl
  | segment p => exact p.transport_metric g v w
  | trans p q hp hq => exact (hq _ _).trans (hp v w)

/-- Reversing a concatenated path inverts the whole transport, including
the reversed order of the pieces. -/
theorem transport_reverse (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) : p.reverse.transport g = (p.transport g).symm := by
  induction p with
  | refl x => rfl
  | segment p => exact p.transport_reverse g
  | trans p q hp hq =>
    change (q.reverse.transport g).trans (p.reverse.transport g) =
      ((p.transport g).trans (q.transport g)).symm
    rw [hp, hq]
    rfl

theorem hasParallelLift_reverse_iff (g : LorentzMetric σ d M) {x y : M}
    (p : PiecewisePath d M x y) (v : TM x) (w : TM y) :
    p.reverse.HasParallelLift g w v ↔ p.HasParallelLift g v w := by
  rw [hasParallelLift_iff, hasParallelLift_iff, transport_reverse]
  constructor
  · intro h
    rw [← h, ContinuousLinearEquiv.apply_symm_apply]
  · intro h
    rw [← h, ContinuousLinearEquiv.symm_apply_apply]

end PiecewisePath
end ProjectAInos.SmoothGeometry

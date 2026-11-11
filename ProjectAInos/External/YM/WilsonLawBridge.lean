module

/-
Adapted from WilsonBridge.lean in yang-mills-group/OpenAI-YM-20261028,
commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464 (Apache-2.0).
Only the finite Wilson-law comparison is imported: the upstream extraction
family and continuum-limit bridge are deliberately not imported here.
See ProjectAInos/External/YM/PROVENANCE.md and NOTICE.
-/

public import ProjectAInos.External.YM.PublicWilson
public import ProjectAInos.External.YM.Wilson.Law

@[expose] public section

/-!
# The two finite Wilson measures are the same measure

The public challenge API and the internal lattice API both use the closed
matrix image of the gauge group, the same oriented plaquettes, and normalized
Haar measure. This file proves those identifications instead of relying on
two merely similar definitions.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

namespace YangMills

open MeasureTheory YM.Lattice
open scoped BigOperators Topology Matrix.Norms.Frobenius

/-- Forget the explicitly specified Lie algebra, retaining the same closed
matrix group used for finite Wilson lattice configurations. -/
def GaugeGroup.core (g : GaugeGroup) : YM.Gauge :=
  ⟨g.n, g.image, g.imageClosed⟩

/-- Both APIs sum the same matrix-trace energy over the same oriented faces. -/
theorem wilsonEnergy_eq_core {g : GaugeGroup} {l : ℕ+}
    (U : Configuration g l) :
    wilsonEnergy U = YM.Wilson.energy (G := g.core) U := by
  apply Finset.sum_congr rfl
  intro p _
  have face : YM.Lattice.faceValue U p =
      plaquette U p.1 p.2.val.1 p.2.val.2 := by
    simp only [YM.Lattice.faceValue, YM.Lattice.square, YM.Lattice.travel,
      YM.Lattice.Step.pos_read, YM.Lattice.Step.neg_read,
      YM.Lattice.Step.vec_neg, YM.Lattice.Step.vec_pos, mul_one,
      plaquette, YM.Lattice.step]
    congr 4 <;> abel_nf
  rw [show g.core.price (YM.Lattice.faceValue U p) =
      g.core.price (plaquette U p.1 p.2.val.1 p.2.val.2) from
      congrArg g.core.price face]
  rfl

/-- With the canonical probability Haar measure, the public Wilson law is
exactly the already normalized, gauge-invariant law in `YM.Wilson`. -/
theorem wilsonLaw_eq_core (g : GaugeGroup) (l : ℕ+) (β : ℝ) :
    wilsonLaw g l β g.core.probHaar = YM.Wilson.law g.core l β := by
  simp only [wilsonLaw, wilsonEnergy_eq_core]
  rfl

/-- On this compact, second-countable matrix group, every normalized Haar
measure in the public `WilsonFamily` is the canonical probability Haar. -/
theorem WilsonFamily.haar_eq_core {g : GaugeGroup} (C : WilsonFamily g) :
    C.haar = g.core.probHaar := by
  haveI : IsProbabilityMeasure C.haar := C.probability
  haveI : C.haar.IsHaarMeasure := C.invariantHaar
  have hiff := @Measure.haarMeasure_eq_iff g.core.El
    (inferInstance : Group g.core.El)
    (inferInstance : TopologicalSpace g.core.El)
    (inferInstance : IsTopologicalGroup g.core.El)
    (YM.Gauge.elMeasurableSpace g.core)
    (YM.Gauge.elBorelSpace g.core)
    (inferInstance : SecondCountableTopology g.core.El)
    g.core.allElements C.haar
    (inferInstance : SigmaFinite C.haar)
    (inferInstance : C.haar.IsMulLeftInvariant)
  exact (hiff.2
    (show C.haar Set.univ = 1 from measure_univ)).symm

/-- The Wilson measure in every public `WilsonFamily` agrees with the
internally proved probability and symmetry law, without extra assumptions. -/
theorem WilsonFamily.law_eq_core {g : GaugeGroup}
    (C : WilsonFamily g) (N p : ℕ) :
    wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar =
      YM.Wilson.law g.core (C.period p * C.denominator N) (C.beta N p) := by
  rw [C.haar_eq_core]
  exact wilsonLaw_eq_core g _ _

/-- The finite lattice moments used by `WilsonFamily.Converges` are literally
integrals against the normalized gauge-invariant Wilson law. -/
theorem WilsonFamily.finiteMoment_eq_core {g : GaugeGroup} (C : WilsonFamily g)
    (N p : ℕ) {n : ℕ} (labels : Fin n → C.Token)
    (x : Fin n → Site (C.period p * C.denominator N)) :
    C.finiteMoment N p labels x =
      ∫ U, (∏ i, C.insertion N p (labels i) (x i) U)
        ∂YM.Wilson.law g.core (C.period p * C.denominator N) (C.beta N p) := by
  unfold WilsonFamily.finiteMoment
  rw [C.law_eq_core]
  rfl

end YangMills

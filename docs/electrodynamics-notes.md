# Electrodynamics Formalization Notes

These notes record mathematical distinctions and interface decisions in `ProjectAinos/Electrodynamics`. They complement the [research plan](cinfty-electrodynamics.md) with its [ledger](cinfty-electrodynamics.md#ledger) and the [guide](electrodynamics.md). Each entry distinguishes proved results from targets. Add an observation that changes an interface, or corrects an earlier judgement, as a numbered entry with a link to the proof.

## ED01. The uniform field of the examples is in a gauge that depends on the time

**Observation.** `Examples.uniformPotential E B` is the potential `−E t dx + B y dz`. Its field is the uniform field with the electric component `E` and the magnetic component `B`, and `hyperbola_stationary` is proved for it. The Hamiltonian of a charge in the canonical phase space (target E9a) is a function of the positions and the momenta only, so it needs potentials that do not depend on the time. The uniform electric field has such a potential, `φ = −E x`, in another gauge.

**Interface decision.** The uniform fields of §§20–22 are instances of E9a in a static gauge. The comparison with the existing example goes through the gauge transformation between the two potentials, for which `stationary_gauge_iff_on` and `chargedAction_gauge_on` exist. The existing example is not changed.

**Proof status.** The static example and the comparison are targets. [Examples](../ProjectAinos/Electrodynamics/Examples.lean) · [Gauge transformations of the action](../ProjectAinos/Electrodynamics/GaugeAction.lean)

## ED02. The example with a source has no potential on flat spacetime yet

**Observation.** The field `t dt ∧ dx`, whose source is `−∂x`, exists as a form on the Minkowski manifold (`Curved.Examples.electric`). The action of the field is a functional of a potential on flat spacetime (`VacuumAction.lagrangian`), and no potential with this field is defined; `uniformPotential` has a constant field. The density `t²/2` of the action is not integrable over the whole spacetime.

**Interface decision.** The regression of the action with a prescribed source uses a new potential `(t²/2) dx` on a bounded open set. `Curved.excitation_flat` relates its excitation to the form on the manifold, so that the sign of the source is the one fixed by `Curved.Examples.electric_source`.

**Proof status.** The action with a source is the target E15. [Vacuum action](../ProjectAinos/Electrodynamics/VacuumAction.lean) · [The example with a source](../ProjectAinos/Electrodynamics/CurrentExamples.lean)

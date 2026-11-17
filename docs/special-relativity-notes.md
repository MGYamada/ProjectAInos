# Special Relativity Formalization Notes

These notes record mathematical distinctions and interface decisions in `ProjectAinos/SpecialRelativity` and in the Minkowski geometry that it uses. They complement the [research plan](cinfty-special-relativity.md) with its [ledger](cinfty-special-relativity.md#ledger) and the [guide](special-relativity.md). Each entry distinguishes proved results from targets. Add an observation that changes an interface, or corrects an earlier judgement, as a numbered entry with a link to the proof.

## SR01. The particle action is fixed to three space dimensions

**Observation.** The geometry of `SmoothGeometry/Minkowski` and the kinematics (`Velocity d`, `boost`, `properTime`) are stated for `d` space dimensions. The action is not: `Spacetime` is `MinkowskiModel 3`, and `freeLagrangian`, `timelikeJets`, `kineticMomentum` and `free_stationary_iff` are stated for it. The research plan writes its targets for `d` dimensions; for example it gives the rank of the Hessian of the action in the velocity as `d`.

**Interface decision.** New statements that do not mention the existing action are made for every `d`: the Hamiltonian on the canonical phase space, the mass shell and its reduction, the collisions, the invariant measure. A statement that compares with the existing action is made for `d = 3`, and the ledger row says so. The existing declarations keep their names and types, since `Electrodynamics` and `GeneralRelativity` use them.

**Proof status.** No statement is changed by this note. The targets SR-D2 and SR-D4 are the first that compare with the action. [Particle action](../ProjectAinos/SpecialRelativity/ParticleAction.lean) · [Spacetime](../ProjectAinos/SpecialRelativity/Spacetime.lean)

## SR02. The norm of a co-ordinate space is not the Euclidean length

**Observation.** `MinkowskiModel d` is `Fin (d + 1) → ℝ`, and the canonical phase space is a ring of functions on `ι ⊕ ι → ℝ`. The norm of these spaces of functions is the greatest absolute value of a co-ordinate. The Euclidean length appears only on `Minkowski.Space d`, which is `EuclideanSpace ℝ (Fin d)`. So `‖p‖` in a formula such as `√(m² + ‖p‖²)` or `‖q̇‖ < 1` is the wrong quantity when `p` is an element of `Fin d → ℝ`. The rest space of an observer has no norm of its own either: `Observer.restForm` is a bilinear form, and `Observer.restForm_posDef` says that it is positive definite.

**Interface decision.** In the free C∞-ring and in the analytic model on `Fin d → ℝ`, write the sum of the squares of the co-ordinates. For the velocity measured by an observer, define the length from `restForm`. The Euclidean norm is used where the existing API has `Minkowski.Space d`.

**Proof status.** The decision applies to the targets SR-D3, SR-D4, SR-D5 and SR-D7. [Minkowski co-ordinates](../ProjectAinos/SmoothGeometry/Minkowski/Basic.lean) · [Observers](../ProjectAinos/SmoothGeometry/Minkowski/Observer.lean)

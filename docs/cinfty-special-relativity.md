# Research Plan for Special Relativity over C∞ Geometry

A Lean formalization programme for Landau and Lifshitz, *The Classical Theory
of Fields*, fourth revised English edition, Chapters I–II, §§1–14.

This is the first part of the relativity and fields trilogy requested in
[issue #8](https://github.com/MGYamada/ProjectAinos/issues/8). Its companions are
[C∞ electrodynamics](cinfty-electrodynamics.md) and
[C∞ general relativity](cinfty-general-relativity.md). The design follows the
mathematical statements, prerequisite tiers, section correspondence and evidence
ledger of [C∞ mechanics](cinfty-mechanics.md), using the constructed shared
geometry rather than the mechanics manuscript's earlier proposed architecture.
The proof-status baseline is `main` at
[`8bb80ce`](https://github.com/MGYamada/ProjectAinos/commit/8bb80ce), reviewed
on 17 November 2026. [After the mechanics programme](#after-the-mechanics-programme)
records the completed mechanics prerequisites used by the proposed SR proofs.

## Implementation plan and current progress

The [research plan](../README.md) assigns Minkowski geometry and kinematics to
§3.1 and relativistic particle dynamics to §3.2. The
[SR implementation guide](special-relativity.md) records the former, while
[`ParticleAction.lean`](../ProjectAinos/SpecialRelativity/ParticleAction.lean)
already supplies part of the latter. Each implemented entry refers to the
cited Lean definitions and theorems in their stated scope. Proposed names later
in this document identify design targets.

| Programme component | Baseline status | Public implementation or remaining task |
| --- | --- | --- |
| C∞ real spectra, structure sheaves, schemes, open restrictions and gluing | Implemented | Shared `SmoothAlgebra` and `SmoothGeometry`; see the [geometry guide](smooth-geometry.md) |
| Manifold-to-scheme construction and affine Minkowski comparison | Implemented | `Manifold.scheme`, `Manifold.schemeMap`, `LorentzManifold.toScheme`, `minkowskiSchemeIso` |
| Lorentz signatures, causal cones, affine causal order and metric duality | Implemented with proofs | `Minkowski.{Convention,Basic,Causal,Dual}` |
| Lorentz/Poincaré maps and observer rest spaces | Implemented with proofs | `Minkowski.{Isometry,Matrix,Affine,Observer}` |
| Boosts, velocity transformations and collinear rapidity | Implemented with proofs | `SpecialRelativity.{Boost,Velocity,Rapidity}` |
| Proper time and normalized timelike four-velocity | Implemented with stated regularity | `ProperTime`; null proper time is separate |
| Massive free action, momentum covector and stationarity iff Euler–Lagrange | Implemented on timelike jets | `SpecialRelativity.free_stationary_iff` in `ParticleAction` |
| Observer energy, coordinate-time Hamiltonian and systematic free-particle Noether theory | Targets | Build on the existing free action; do not replace it |
| Mass-shell integration, distributions and invariant collision rates | Targets | A measure-theoretic interface is needed in addition to the shell equations |
| Decays, scattering kinematics and angular-momentum charges | Targets | Finite-particle algebra first; interaction dynamics are additional premises |
| Canonical Poisson structures, Poisson morphisms, quotients by ideals and reduced Poisson rings | Implemented in the shared algebra by the mechanics programme | `PhaseSpace.canonical`, `IsPoissonHom`, `SmoothRingCon.ofIdeal`, `PoissonStructure.Reduction`; prerequisites of SR-C6, SR-D7 and SR-D8 |
| Hamilton's equations along curves, the Legendre correspondence with an inverse morphism, cyclic co-ordinates | Implemented in `Mechanics` for free C∞-rings | `IsTrajectory`, `VelocitySpace.IsHyperregular`, `CyclicReduction`; the velocity ball of SR-D4 is not a free ring in the velocity |
| Universal C∞ cotangent comparison and nonreduced families of solutions | Research targets | Not consequences of the present manifold-to-scheme functor |

The existing `Electrodynamics.mass_shell` is a downstream verification of the
normalization of `m • fourVelocity v`. It is not evidence that a complete
SR momentum, collision or mass-shell measure API already exists.

### Ledger

The ledger gives one status to each of §§1–14, with the vocabulary of the
[mechanics ledger](cinfty-mechanics.md#ledger): *proved* (Lean, no `sorry`,
axioms audited), *proved modulo interface*, *hypothesis*, *evidence* (computer
algebra only), or *informal*. The status refers to the target of the row in the
[dictionary](#landau-lifshitz-correspondence), whose last column records the
baseline. A status is only promoted, and a row whose target is proved only in
part stays at the lower status, with the proved part named. A row is closed
when it is *proved*, or when its remark names the proved part and gives the
reason why the rest is not proved; the rows closed in the second way are
listed after the count. The wave names F1–F26 are those of
[issue #135](https://github.com/MGYamada/ProjectAinos/issues/135), which tracks
completion.

| § | Topic | Status | Lean declarations, or what is missing |
|---:|:---|:---|:---|
| 1 | Finite signal speed | proved | `futureCausal_convex`, `causallyPrecedes_refl`, `causallyPrecedes_trans`, `causallyPrecedes_antisymm`, `causallyPrecedes_poincare`, `IsCausalRelation.transform`, `IsCausalRelation.not_of_spacelike`, `IsCausalRelation.clock_pos`, `IsCausalRelation.restForm_le_clock_sq`. Scope: a relation between the events of Minkowski space with `d` space dimensions. That the relation is contained in the causal order is the hypothesis `IsCausalRelation`; it is the physical premise that no signal is faster than light |
| 2 | Intervals | proved | `intervalSq`, `Timelike`, `Spacelike`, `Lightlike`, `Causal`, `LorentzGroup.preserves_interval`, `LorentzGroup.timelike_iff`, `LorentzGroup.spacelike_iff`, `LorentzGroup.lightlike_iff`, `PoincareGroup.preserves_interval`, `timelike_convention`. Scope: real Minkowski space with `d` space dimensions, both sign conventions |
| 3 | Proper time | proved | `properTime`, `properTime_integrable`, `properTime_poincare`, `properTime_reparametrize`, `properTime_inertial`, `properTime_timeDilation`, `TimelikeSegment.futureTimelike_displacement`, `TimelikeSegment.properTime_le_properSpeed`, `TimelikeSegment.properTime_eq_properSpeed_iff`, `sum_properTime_le_properSpeed`. Scope: `d` space dimensions; curves that are `C¹` near every point of a compact segment with a future timelike velocity, and finitely many such pieces with matching endpoints |
| 4 | The Lorentz transformation | proved | `LorentzGroup`, `properLorentzGroup`, `orthochronousLorentzGroup`, `matrix_preserves_metric`, `matrix_det_eq_one_or_neg_one`, `boost`, `boost_time`, `boost_space`, `boost_future`, `boost_neg_inverse`, `boost_det`, `rotationGroup`, `rotationPart_mem`, `rotationPart_mul_boost`, `eq_of_mul_boost_eq`, `boostPart_eq_zero_iff`, `boostPart_boost_mul_boost`, `wignerRotation_mul_boost`, `boost_collinear_mul`, `wignerRotation_collinear`. Scope: every orthochronous transformation is factored in the frame of the co-ordinates as a rotation after a boost, in one way only; the rotation that remains in a product of two boosts is defined by this factorization, and its angle is not computed |
| 5 | Transformation of velocities | proved | `Velocity.observerEquiv`, `Velocity.transform`, `Velocity.norm_transform_lt_one`, `Velocity.transform_boost`, `transform_collinear`, `rapidity_add`, `composed_speed_lt_one`. Scope: the orthochronous group acts on the open ball of velocities; velocities that are not collinear are composed by this action, and collinear ones by the addition of rapidities |
| 6 | Four-vectors | informal | Proved: `flat`, `sharp`, `flat_natural`, and the tensor operations of the [shared geometry](smooth-geometry.md). Missing: the universal C∞ cotangent module and its comparison with the cotangent bundle (SR-F2, F26) |
| 7 | Four-dimensional velocity | proved | `fourVelocity_unit`, `fourVelocity_metric`, `properTime_null`, `pair_fourVelocity_deriv`, `FutureShell.chart`, `FutureShell.mem_shell_zero_iff`, `FutureShell.zero_notMem_shell`, `Einbein.stationary_iff`, `Einbein.lagrangian_eliminate`, `Einbein.fourVelocity_eq_of_stationary`, `Einbein.stationary_massless_iff`, `Einbein.deriv_eq_smul_of_stationary_massless`, `Einbein.action_reparametrize`. Scope: the orthogonality of the acceleration for a `C²` curve in three space dimensions; the shells and the action with an auxiliary field in `d` dimensions, for `C²` pairs `(x, e)` with `e > 0` on `[a, b]`; the comparison with the action `−m ∫ ds` in three dimensions |
| 8 | The principle of least action | proved | `freeAction`, `freeLagrangian_contDiffOn`, `free_momentum`, `free_stationary_iff`, `free_stationary_iff_fourVelocity_const`, `free_stationary_iff_inertial`, `hasFDerivAt_kineticMomentum`, `ker_velocityHessian`, `finrank_range_velocityHessian`; for the mass shell `MassShell.isCoisotropic_shellIdeal`, `MassShell.normalizer_shellIdeal_le`, `MassShell.isPoissonHom_toShellCoordinates`, `MassShell.reductionHom_bijective`, `MassShell.isPoissonHom_reductionHom`, `MassShell.initialData_p_zero`. Scope: the action in three space dimensions, `C²` curves with a timelike velocity on `[a, b]`, and `m ≠ 0` for the inertial motion; the mass shell in `d` dimensions, its future sheet and the reduction for `(−+++)` |
| 9 | Energy and momentum | proved | `kineticMomentum`, `kineticMomentum_eq`, `sharp_kineticMomentum`, `metric_smul_fourVelocity`; the Hamiltonian on all momenta (SR-D7: `FreeParticle.hamiltonian`, `FreeParticle.isTrajectory_iff`, `FreeParticle.sum_sq_hamiltonianField_lt_one`, `FreeParticle.isIntegral_angularMomentum`, `FreeParticle.realCurve_eq_motion`, `FreeParticle.flowDomain_hamiltonianField`); the energy and the momentum measured by an observer (SR-D3: `observerEnergy_pos`, `observerEnergy_sq`, `restForm_observerVelocity_lt_one`, `observerEnergy_transform`, `observerEnergy_change`); the Legendre transformation (SR-D4: `FreeParticle.velocityOfMomentum_legendre`, `FreeParticle.legendre_velocityOfMomentum`, `FreeParticle.energy_eq_relEnergy`, `FreeParticle.stationary_iff_deriv_const`, `FreeParticle.isTrajectory_iff_legendre`, `FreeParticle.free_stationary_graph_iff`); the shell (SR-D5: `FutureShell.chart`, `FutureShell.contDiffOn_point`, `FutureShell.lorentz_mem_shell`, `FutureShell.contDiffOn_action`, `FutureShell.action_mul`, `FutureShell.scheme`, `FutureShell.lift_futureShellFunction_eq_zero_iff`); the expansion in `1/c` (SR-K5: `Newtonian.abs_energy_sub_le`, `Newtonian.abs_lagrangian_sub_le`, `Newtonian.abs_momentum_sub_le`, `Newtonian.abs_clockRate_sub_le`). Scope: `d` space dimensions, and three for the comparison with the action of space-time. The shell is a graph with one chart, in which the Lorentz group acts smoothly; the automorphisms of its C∞ scheme are not constructed, and the comparison with the ideal of the future sheet is for real points and `m > 0`. The expansion is for functions of the velocity, not for trajectories |
| 10 | Transformation of distribution functions | proved | `FutureShell.measure`, `FutureShell.map_action_measure`, `FutureShell.integral_comp_action`, `FutureShell.numberCurrent_transform`, `FutureShell.numberDensity_transform`, `FutureShell.time_numberCurrent`, `FutureShell.numberFlux_transform`, `FutureShell.numberFlux_hyperplane`. Scope: `d` space dimensions and every mass, the mass zero included; the measure `dᵈπ/E` in the chart of the shell; the number of particles through a hypersurface that is given by a surface measure on the events and a field of normals. The two are constructed for the hyperplanes of the co-ordinates; for another hypersurface they are data, and no theorem derives them from the hypersurface. The equality of the numbers through different hypersurfaces needs a transport equation and is not treated |
| 11 | Decay of particles | proved | `invariantMass_add_le`, `intervalQuadratic_add_eq_zero_iff`, `centreOfMomentum`, `eq_centreOfMomentum`, `not_exists_observer_of_null`, `TwoBodyDecay.energy_first`, `TwoBodyDecay.energy_second`, `TwoBodyDecay.momentum_add`, `TwoBodyDecay.momentum_sq_first`, `TwoBodyDecay.mass_add_le`, `TwoBodyDecay.eq_smul_of_threshold`, `exists_twoBodyDecay`. Scope: the decay into two particles, in `d` space dimensions; the energies in another frame are given by `observerEnergy_change`. The distribution of the directions and the decay into more than two particles are not treated |
| 12 | Invariant cross-section | proved modulo interface | Proved: `fluxFactor_lorentz`, `fluxFactor_sq`, `fluxFactor_target_at_rest`, `measurePreserving_action_prod`, `crossSection_covariant`. Interface: a measure on the final states that the Lorentz group preserves, and a transition weight that is a Lorentz scalar. Not proved: the construction of this measure on the set where the total momentum is conserved. It needs a coarea formula or a construction with distributions, and the pinned Mathlib has no coarea formula. Special relativity does not determine the weight |
| 13 | Elastic collisions of particles | proved | `mandelstam_sum`, `ElasticCollision.energy_eq`, `ElasticCollision.momentum_sq_eq`, `ElasticCollision.mandelstamT_eq`, `ElasticCollision.mandelstamT_nonpos`, `exists_elasticCollision`, `mandelstamS_target_at_rest`, `mandelstamT_elastic_target_at_rest`. Scope: the invariants `s`, `t`, `u` and the frame of the centre of momentum, in `d` space dimensions; for a target at rest, `s` and `t` in terms of the energies. The angles in the frame of the target are not computed |
| 14 | Angular momentum | proved | `Poincare.canonical_lorentzCharge_p`, `Poincare.canonical_lorentzCharge_lorentzCharge`, `Poincare.canonical_boostCharge_p`, `Poincare.canonical_boostCharge_boostCharge`, `Poincare.inertia_zero`, `MassShell.initialData_lorentzCharge_zero_succ`, `MassShell.initialData_lorentzCharge_succ_succ`, `orbitalMoment_lorentz`, `flat_lorentzGenerator`, `kineticMomentum_lorentzGenerator`, `orbitalMoment_eq_of_stationary`, `totalMoment_freeMotion`, `sum_orbitalMoment_same_event`, `totalMoment_add_const`, `centreOfEnergy_sub`, `centreOfEnergy_freeMotion`. Scope: finitely many point particles in `d` space dimensions that move freely or collide in one event; the centre of energy for events that are simultaneous for an observer; the charges as Noether's charges for one free particle in three dimensions. The contribution of fields belongs to electrodynamics |

Count: 12 proved, 1 proved modulo interface, 1 informal.

Closed with a stated remainder: §12 (the measure of the final states on the set where the momentum is conserved, and the transition weight).

### After the mechanics programme

The [mechanics ledger](cinfty-mechanics.md#ledger) records all 52 sections
as *proved* in their stated scopes. The final delivery is recorded in
[#114](https://github.com/MGYamada/ProjectAinos/issues/114). Broader geometric
and constrained mechanics is tracked in
[#132](https://github.com/MGYamada/ProjectAinos/issues/132).

**Prerequisites that now exist.** They are in the shared algebra or in
`Mechanics`, and none imports a relativity module.

| Prerequisite named in this plan | Declarations | What they do not cover |
| --- | --- | --- |
| Derivations with the smooth chain rule (SR-F2) | `SmoothDerivation`, `FreeSmoothRing.derivationEquiv` | The universal module `Ω_A` and its comparison with the cotangent bundle |
| Tangent points as morphisms to dual numbers (SR-F5) | `SmoothRing (DualNumber A)`, `TangentPoint`, `FreeSmoothRing.tangentPointEquiv`, `FreeSmoothRing.presentedTangentPointEquiv` | Coefficient rings other than `ℝ`; Lorentz signature over a nonreduced base |
| Quotients by ordinary ideals (SR-F2) | `SmoothRingCon.ofIdeal`, `SmoothRingCon.ofIdealHomEquiv`, from Hadamard's lemma `SmoothRing.op_sub_op` | Completeness and fairness of the quotient |
| Canonical Poisson API (SR-C6) | `PhaseSpace.canonical`, `IsPoissonHom`, `PhaseSpace.isPoissonHom_of_canonical`, `PoissonStructure.isIntegral_iff_hamiltonian_eq_zero` | Momentum maps of a general group action |
| Constraints and reduction (SR-D8) | `PoissonStructure.isCoisotropic_span`, `PoissonStructure.Reduction`, `PoissonStructure.toReduction_bijective`, `CyclicReduction.canonicalReductionHom_bijective` | The Dirac bracket; reduction by a non-abelian group |
| Hamilton's equations and flow (SR-D4, SR-D7) | `IsTrajectory`, `isTrajectory_canonical_iff`, `NonlinearODE.contDiffOn_flow`, `Mechanics.exists_isTrajectory` under a completeness hypothesis | The relativistic Hamiltonian, its completeness proof, and the time-dependent Hamiltonian formalism |
| Legendre correspondence (SR-D4) | `VelocitySpace.IsHyperregular.isTrajectory_iff_isSolution` | Lagrangians that are smooth only on an open set of velocities; a velocity chart other than the velocity itself, because the momentum is the derivative in the velocity generator |
| Model proofs of a symmetry algebra (SR-C6) | `AngularMomentum.canonical_M_M`, `AngularMomentum.isPoissonHom_momentumMap`, `Galilei.canonical_K_p` | The Poincaré algebra |
| Finite reactions without relativity (SR-C1–C3) | `TwoBody.disintegration_momentum_sq`, `TwoBody.isElastic_iff` | Relativistic shells and thresholds |

**Analytic prerequisites and limits.**

- *Measures.* `Scattering.crossSection_apply` supplies a worked
  change-of-variables proof for a measurable deflection branch, and
  `Mechanics.volume_image_hamiltonianFlow` supplies a phase-volume result on
  the flow domain. For §§10 and 12, SR-I4 still requires the measure on the
  massive and punctured massless shells, its Lorentz pushforward law, and
  the measure and flux factors on the collision constraint locus.
- *Asymptotic statements.* `Variational.exists_second_order_bound` gives a
  uniform second-order remainder for a smooth scalar family on a compact
  parameter set. For SR-K5 and §9, state the compact velocity range and the
  allowed values of `c`. A second-order bound for `γ` in the parameter
  `c⁻²` gives a first-order bound for the rest-energy subtraction after
  multiplying by `mc²`.
- *Domains that are not all of `ℝⁿ`.* A free C∞-ring is the ring of smooth
  functions on all of `ℝⁿ`. Mechanics used three devices for other domains: a
  global chart (`s = log r` for the radius), an adjoined inverse whose
  relation is kept as an element (`1/r` in Kepler's problem), and the
  open-domain analytic model. The velocity ball `‖v‖ < 1` and the timelike
  cone are such domains. A theorem stated for coefficient functions in a free
  ring does not apply to a co-ordinate system with singular coefficients.
  The first device was used for positions, where the conjugate momenta
  change with the chart and the bracket is kept. A chart of the velocities
  is different: the momentum is a derivative in the velocity, and the chart
  changes that derivative (item 4 below).

**Proof design.**

1. *SR-C6 in SR5* uses the canonical Poisson API for a finite list of bracket
   identities on generators, following `AngularMomentum.canonical_M_M`.
   The contraction to the Galilei algebra with mass as its central term
   (`Galilei.canonical_K_p`) is a separate statement about a family in `c`.
2. *SR-D7* treats the coordinate-time Hamiltonian as an element of a
   free ring. It is the Hamiltonian half of SR-D4 and needs no velocity ball.
3. *SR-D8* treats the mass shell as a coisotropic ideal, with its
   reduced ring. It gives the algebraic meaning of the parameter degeneracy
   of SR-D2 and uses the reduction theorem that gave the reduced mass in
   mechanics.
4. *SR-D4 starts on the open velocity ball.* Use the same open-domain
   analytic model as SR-D1 and take the fibre derivative in the physical
   velocity `v`. The inverse momentum map can use the proper velocity
   `w = γv`, with `v = w/√(1 + ‖w‖²)` and `p = m w`. A later free-ring
   comparison in `w` would need the transported vertical derivatives
   `∂/∂vᵢ = Σⱼ (∂wⱼ/∂vᵢ) ∂/∂wⱼ` and the trajectory relation `q̇ = v(w)`.
   [Variational note V06](variational-notes.md#v06-relativistic-fibre-derivatives-use-the-physical-velocity)
5. *SR3 takes the form of `TwoBody`.* Decay and elastic kinematics are real
   vector algebra, with statements of the form "the conservation laws hold
   exactly when the outgoing data are …". The nonrelativistic statements are
   regression targets for the limit.
6. *Completion criterion.* The criterion that closed the mechanics issue is
   adopted for §§1–14. A row is closed when it is proved, or when it names
   its proved part and gives the reason why the rest is not proved. A status
   is only promoted, and a promotion in a restricted scope writes the scope
   in the row. A theorem whose hypotheses are identities in a free C∞-ring
   comes with an instance, because such hypotheses quantify over all values
   of the generators (note M66 of the mechanics notes).

## Abstract

Special relativity supplies the common spacetime and particle language of
classical field theory. This plan treats Minkowski spacetime as an affine
smooth manifold with its actual C∞ structure sheaf, a Lorentz metric, and a
chosen time orientation. Lorentz and Poincaré symmetries act by smooth scheme
isomorphisms. Observers define rest spaces, energies and spatial momenta;
timelike curves carry invariant proper time; particle actions produce
equations of motion under explicit admissibility hypotheses.

The extension from kinematics to dynamics has three distinct parts. Finite
dimensional algebra controls mass shells and collision constraints. Analysis
connects local variations with actual action integrals and constructs invariant
measures. Physical premises choose free-particle actions, conservation laws at
interaction events and rate models. C∞ geometry organizes these parts without
turning empirical premises into axioms or assuming that singular solution
spaces are smooth manifolds.

## Aim and design decisions

The intended reader is a contributor translating the fourteen textbook
sections into Lean statements. Each target must identify its mathematical
objects, hypotheses, conclusion, dependencies and proof status. Existing
theorems are reusable endpoints; statements about additional objects are new
targets even when their coordinate formulas look elementary.

1. **Use the constructed geometry.** Smooth real-point manifolds are the first
   physical models. Their C∞ schemes are constructed, and Poincaré maps already
   act on those schemes. Generalized points and nilpotents remain meaningful
   extension targets, with their comparison theorems stated separately.
2. **Keep common mathematics below physics.** Lorentz linear algebra, forms
   and manifold constructions stay in `SmoothGeometry`. Particle hypotheses
   and interpretations live in `SpecialRelativity`. The shared core does not
   import the project physics modules or the vendored Yang–Mills theory.
3. **Separate equations from dynamics and rates.** A conservation constraint
   determines allowed momenta, not a probability distribution or a scattering
   amplitude. A set of shell equations does not itself supply a measure.
4. **Use coordinate calculations as comparison theorems.** The native metric,
   affine displacement, covector and observer are the primary objects. A
   component identity must be connected to them by proved evaluation laws.

## Conventions and tiers

Physical spacetime has coordinates `(t,x,y,z)`, time first, `c = 1`, metric
`(-+++)` and standard orientation `dt ∧ dx ∧ dy ∧ dz`. Most kinematic results
work with `d` spatial dimensions; cross products and familiar angular momenta
specialize to `d = 3`. The Euclidean norm of `Minkowski.space v` measures
spatial length. The norm on a coordinate-function type is not substituted for
that spatial norm.

The shared API accepts either Lorentz signature explicitly. Write

$$
\langle v,w\rangle_L=v^0w^0-\mathbf v\cdot\mathbf w,
\qquad Q(v)=\langle v,v\rangle_L,
\qquad g(v,w)=-\langle v,w\rangle_L.
$$

Thus timelike means `Q > 0`, whereas the physical metric square is negative.
`Lightlike` excludes zero; `Causal` includes it. Future orientation is a
separate choice from spacetime orientation. Proper Lorentz transformations
preserve orientation; orthochronous transformations preserve the future cone.
Boost formulas below use the passive convention of the existing API.

Momenta with upper indices are vectors. The derivative of a Lagrangian with
respect to velocity is a covector: the implemented `kineticMomentum` is
`m • flat .timeNegative (fourVelocity v)`. Its time component is minus the
energy in the standard observer frame. Raising it gives the momentum vector.
This distinction must remain visible at every action-to-component bridge.

| Tier | Proof prerequisite |
| --- | --- |
| A | Algebra over C∞ rings, modules, or specified algebraic structures; earlier comparison results may be used |
| A* | Concrete finite dimensional polynomial/rational identities and elementary inequalities with their denominators or signs controlled |
| B | Named analytic interfaces: differentiation, integration, ODEs, estimates or measure transport |
| C | Geometry: manifolds, bundles, sheaves, smooth maps, orientations and differential forms |
| D | A substantial theorem awaiting proof, used only as an explicit hypothesis when needed |
| P | A physical or asymptotic argument whose formal replacement must specify a model and hypotheses |

Tiers describe prerequisites, not proof status. A theorem about a real
Minkowski model is not automatically a theorem over every C∞ coefficient
ring. The [ledger](#evidence-and-proof-ledger) distinguishes implemented
results, new proof targets, conditional statements and open research.

## Foundations

### The common C∞ base

For an open spacetime region `U`, observables form `C∞(U)`, with every smooth
finite-arity operation acting pointwise. Restrictions preserve those
operations. The structure sheaf, rather than just the underlying ring at one
global chart, records locality. The present construction supplies the actual
sheaf of smooth functions on a manifold and proves local affineness.

**Existing construction SR-F1 [C].** `Manifold.scheme n M` equips a
boundaryless finite dimensional manifold with its C∞ scheme. A smooth map
induces `Manifold.schemeMap`, respecting identity and composition. The
Minkowski comparison `minkowskiSchemeIso` identifies the resulting scheme
with the constructed spectrum of the smooth algebra of its coordinate model.
The source is the [shared Lorentz interface](../ProjectAinos/SmoothGeometry/Lorentzian.lean)
and the manifold modules documented in the geometry guide.

The metric is additional smooth data on the tangent bundle; changing its
overall sign does not change the scheme. `LorentzManifold.toScheme` does not
assert that all C∞ schemes admit Lorentz metrics. The implemented comparison
also does not establish full faithfulness of the manifold functor or an
isomorphism `A ≅ Γ(Spec A)` for arbitrary C∞ rings.

**Target SR-F2 [A,C].** Construct the universal smooth cotangent module
`Ω_A` and compare it, for the manifold structure sheaf, with sections of the
actual cotangent bundle. The universal derivation must satisfy the full
smooth chain rule, not merely the polynomial Leibniz rule:

$$
d\Phi_f(a_1,\ldots,a_n)
=\sum_i\Phi_{\partial_i f}(a_1,\ldots,a_n)\,da_i.
$$

The comparison must commute with restriction and smooth pullback before
transporting the native metric and tensors into algebraic language. General
C∞ localizations and gluing exist. Since the mechanics programme, so do
quotients by ordinary ideals (`SmoothRingCon.ofIdeal`) and derivations that
satisfy this chain rule (`SmoothDerivation`), which for a free ring are
determined by their values on the generators. The universal cotangent module
with its universal property, completeness theory and the bundle comparisons
are separate remaining stages. No SR milestone below silently assumes them.

### Affine events, vectors and symmetries

An event is a point of an affine space modeled on `V = ℝ^(1+d)`. Displacements
belong to `V`; no physical equation should depend on the chosen affine origin.
The implementation uses the standard coordinate carrier for convenient
calculation, while `CausallyPrecedes` already works with affine displacement.

**Existing construction SR-F3 [A*,C].** `LorentzGroup d` consists of invertible
linear maps preserving the normalized pairing. `matrix_preserves_metric`
gives `Lᵀ g L = g`, and `matrix_det_eq_one_or_neg_one` gives the determinant
alternatives. `PoincareGroup.ofLinearTranslation L a` acts by `x ↦ Lx+a`;
[`PoincareGroup.toSchemeIso`](../ProjectAinos/SmoothGeometry/Minkowski/Affine.lean)
constructs its actual smooth scheme isomorphism.

For observables, the same transformation acts contravariantly by composition.
A future geometry target is to expose this compatibility directly as a
commuting square between scheme pullback and `C∞(U)` pullback. It is a
comparison API, not a second definition of the Poincaré group.

**Existing construction SR-F4 [A*,C].** An `Observer d` is a future unit
timelike vector `u`. Its clock is `θᵤ(v)=−g(u,v)`, its rest space is the clock
kernel, and its spatial projection is `v−θᵤ(v)u`. The implemented
`Observer.split`, `restSpace_finrank`, `restForm_posDef`, `clock_transform`
and `project_transform` prove unique decomposition, dimension, positivity
and covariance. These are the common inputs to particle measurements and
the electric/magnetic decomposition in the ED manuscript.

### Real causal geometry and infinitesimal extensions

The closed future cone is convex, pointed and stable under nonnegative
scaling. Therefore `q−p` in this cone defines an affine partial order.
This is an implemented property of a real Lorentz vector space. The assertion
that interactions propagate inside the cone is a physical premise about a
chosen theory, not a consequence of convexity.

**Target SR-F5 [A,C; research].** For a C∞ algebra `A` and its dual-number
extension, a generalized tangent point should be a smooth morphism
`A → B[ε]/(ε²)`. On ordinary Minkowski space it must reproduce the actual
native tangent vector and derivative. A Lorentz form on a finite projective
module can be specified algebraically, but signature, future orientation
and positivity must be interpreted on real fibres or by a separately proved
notion over the base. Ordering an arbitrary nonreduced ring is not assumed.

For `B = ℝ` the first half exists. `TangentPoint A` is the type of morphisms
`A → ℝ[ε]`. For a free ring these are the pairs of a point and a vector, and
for a ring presented by equations they are the pairs that satisfy the
equations and their linearizations. The comparison with the native tangent
vector of Minkowski space, and coefficients other than `ℝ`, remain targets.

Null constraints can retain infinitesimal information at singular points.
In particular the cone vertex is not discarded when studying a scheme of
constraints, but it is excluded from the physical massless particle shell.
The physical smooth locus and a nonreduced constraint space have different
contracts; their coincidence is never inferred from equality of real points.

## Kinematics and clocks

### Boosts and relative velocities

For `‖β‖<1`, let `γβ=(1−‖β‖²)^(-1/2)`. The existing boost is constructed
using Lorentz reflections, so zero velocity needs no exceptional division.
Its coordinate formula is

$$
t'=\gamma_\beta(t-\boldsymbol\beta\cdot\mathbf x),
\qquad
\mathbf x'=\mathbf x+
\left(\frac{\gamma_\beta^2}{1+\gamma_\beta}
\boldsymbol\beta\cdot\mathbf x-\gamma_\beta t\right)\boldsymbol\beta.
$$

**Existing result SR-K1 [A*,B].** `boost_time`, `boost_space`, `boost_future`,
`boost_neg_inverse` and `boost_det` prove the component formula, future
preservation, inverse and properness. `Velocity.observerEquiv` identifies
velocities with observers; the orthochronous Lorentz group acts on the open
velocity ball. `Velocity.norm_transform_lt_one` supplies subluminality.

For collinear velocities the passive law is `(a−b)/(1−ab)`. Rapidity
`artanh b` is additive for the corresponding active composition
`(a+b)/(1+ab)`. The signs must be checked before identifying these formulas.
The existing theorem covers collinear rapidities; it does not collapse a
product of arbitrary boosts to a single boost.

**Target SR-K2 [A*,B,C].** Factor a proper orthochronous Lorentz transformation
relative to a chosen observer into a standard boost and a rest-space
orthogonal map. Obtain the residual rotation in the composition of two
noncollinear boosts from this factorization. Prove uniqueness with the
factor order fixed, then derive its zero and collinear special cases. This
supplies a controlled extension for Wigner rotations rather than an invalid
commutative velocity-addition rule.

*Status.* Proved in
[`SpecialRelativity/Factorization.lean`](../ProjectAinos/SpecialRelativity/Factorization.lean)
for every orthochronous transformation and the observer of the co-ordinate
frame, with the factor order rotation after boost.

### Proper time and maximal inertial clocks

For a future timelike curve on `[a,b]`, define

$$
\tau[\gamma]=\int_a^b\sqrt{Q(\dot\gamma(s))}\,ds,
\qquad U=\frac{\dot\gamma}{\sqrt{Q(\dot\gamma)}}.
$$

**Existing result SR-K3 [B].** `properTime_integrable` uses C¹ regularity near
every point of the closed parameter interval. `properTime_poincare` proves
affine-isometry invariance. `properTime_reparametrize` permits a C¹ parameter
map with nonnegative derivative, including zeros; it is an integral
substitution theorem, not an inverse-function theorem. `fourVelocity_unit`
and `fourVelocity_metric` require timelikeness and give `Q(U)=1`, `g(U,U)=−1`.
`properTime_null` proves zero elapsed proper time for null derivatives.

**Target SR-K4 [A*,B].** If `γ` is C¹, future timelike on a compact segment,
and `a<b`, its displacement `Δ=γ(b)−γ(a)` is future timelike and

$$
\tau[\gamma]\leq\sqrt{Q(\Delta)}.
$$

Equality holds exactly when all tangent vectors are positive scalar
multiples of one fixed future unit vector. Thus the maximizing curve is an
inertial segment up to increasing reparametrization, not necessarily affine
in the supplied parameter. Prove the reverse Cauchy–Schwarz inequality by
the existing observer split; integrate it against the observer determined
by `Δ`; use continuity for the equality case. Piecewise C¹ curves follow
by finite subdivision with matching endpoints. No assertion compares clocks
whose endpoints or admissibility conditions differ.

*Status.* Proved in
[`SpecialRelativity/MaximalProperTime.lean`](../ProjectAinos/SpecialRelativity/MaximalProperTime.lean).
The case of equality is stated for a single `C¹` piece.

### Restoring the light-speed parameter

The baseline APIs use `c=1`. A dimensional comparison should explicitly use
`x⁰=ct`, `β=v/c`, momentum vector `(E/c,p)`, and metric `(-+++)` on those
coordinates. Proper time in physical seconds is `c⁻¹∫sqrt(-g(dx,dx))`.
This prevents a change of units from being mistaken for a limit theorem.

**Target SR-K5 [B].** For a fixed velocity bound `V` and `c≥2V` with `c>0`,
prove uniform Taylor remainder estimates for `γ(v/c)`, clock rates and the
free-particle energy on `‖v‖≤V`. State constants in terms of `m` and `V`.
The limit of a trajectory requires a separate stability argument; estimates
for a Lagrangian or momentum function alone do not prove trajectory convergence.

*Status.* Proved in
[`SpecialRelativity/NewtonianExpansion.lean`](../ProjectAinos/SpecialRelativity/NewtonianExpansion.lean)
for the energy, the Lagrangian, the momentum and the rate of a clock, with
the constants `|m| V⁴/(2c²)`, `|m| V³/c²` and `V⁴/(2c⁴)`. The limit of a
trajectory is not stated.

## Relativistic particle dynamics

### The free action and its degeneracy

For positive mass and timelike reference velocities, the action is

$$
S_m[\gamma]=-m\int_a^b\sqrt{-g(\dot\gamma,\dot\gamma)}\,ds.
$$

**Existing result SR-D1 [B].** `timelikeJets` is open,
`freeLagrangian_contDiffOn` gives the needed regularity there, and
`free_stationary_iff` proves fixed-endpoint stationarity iff the
Euler–Lagrange residual vanishes on `(a,b)`, assuming `a<b`, a C² path and
timelikeness throughout `[a,b]`. The action is an actual interval integral.
The differentiability argument does not extend the square root smoothly
across the null cone.

Its velocity derivative is the implemented momentum covector

$$
\pi=mU^\flat,\qquad p=\pi^\sharp=mU,
\qquad g(p,p)=-m^2.
$$

**Target SR-D2 [A*,B].** Prove directly in the SR layer that positive-mass
free stationarity is equivalent to constancy of `U`, hence to an inertial
image with a regular timelike reparametrization. Compute the velocity
Hessian and show that its kernel is exactly the span of the velocity.
Its rank is `d`, reflecting parameter invariance. A globally invertible
Legendre transform on all spacetime velocities is therefore inappropriate.
The existing curved particle variation theorems provide an independent
Minkowski specialization; SR must not import GR to obtain its basic result.

*Status.* Proved in
[`SpecialRelativity/FreeMotion.lean`](../ProjectAinos/SpecialRelativity/FreeMotion.lean)
for `m ≠ 0`, in three space dimensions.

The physical selection of the length action remains a premise. A possible
uniqueness theorem assumes locality, dependence only on velocity, Lorentz
invariance and positive one-homogeneity on a connected timelike cone. These
assumptions reduce the Lagrangian to a constant multiple of proper speed.
Choosing the constant `−m` is the physical normalization, not an algebraic
consequence of Lorentz symmetry alone.

### Energy and the coordinate-time Hamiltonian

**Target SR-D3 [A*].** For a future unit observer `u` and future massive
momentum `p`, define `Eᵤ=−g(u,p)` and `p⊥=p−Eᵤu`. Prove

$$
p=E_u u+p_\perp,\qquad E_u>0,
\qquad E_u^2=m^2+g(p_\perp,p_\perp),
\qquad \mathbf v_u=p_\perp/E_u.
$$

Use rest-space positivity to show `‖vᵤ‖<1`, with the norm supplied by the
rest-space metric. Jointly transforming the observer and particle leaves
energy unchanged. Changing only the observer gives the familiar energy and
momentum transformation formulas.

*Status.* Proved in
[`SpecialRelativity/ObserverEnergy.lean`](../ProjectAinos/SpecialRelativity/ObserverEnergy.lean).
The change of the observer is stated for the energy,
`E' = γ E − ⟨γ w, p⊥⟩`.

**Target SR-D4 [A*,B].** Fix an inertial observer and use its time as the
parameter. For `m>0`, the spatial Lagrangian has an invertible fibre derivative:

$$
L(\mathbf v)=-m\sqrt{1-\|\mathbf v\|^2},\qquad
\mathbf p=m\gamma\mathbf v,\qquad
H(\mathbf p)=\sqrt{m^2+\|\mathbf p\|^2}.
$$

Construct the inverse `v=p/sqrt(m²+‖p‖²)` and prove the Legendre identities
and Hamilton equations. This transform is on the spatial velocity ball;
it is compatible with, but different from, the degenerate spacetime action.
Free spatial momentum and energy are conserved. After restoring units,

$$
E=mc^2\gamma(\mathbf v/c),\qquad
E-mc^2=\tfrac12m\|\mathbf v\|^2+O(c^{-2}).
$$

The `O(c⁻²)` statement uses the uniform compact-velocity contract SR-K5.
Subtracting the constant rest energy preserves Hamilton's equations.

*Status.* Proved in
[`SpecialRelativity/SpatialLegendre.lean`](../ProjectAinos/SpecialRelativity/SpatialLegendre.lean)
for `m > 0`: the two maps are inverse to each other, the energy is
`√(m² + Σ pᵢ²)`, Lagrange's and Hamilton's equations correspond, and in three
space dimensions the action of space-time is stationary on a graph if and
only if this action is stationary on the curve.

**Target SR-D7 [A].** For `m > 0` the function `√(m² + ‖p‖²)` is smooth on
all momenta, so `H` is an element of the canonical phase space
`PhaseSpace (Fin d)` of the shared algebra. Prove with
`isTrajectory_canonical_iff` that along a trajectory `p` is constant and
`q̇ = p/H`, that `‖q̇‖ < 1`, and that the momentum, the energy and the orbital
angular momentum are integrals of the motion. This uses the canonical bracket
and no velocity chart. The explicit trajectory
`(q₀ + t · p₀ / H(p₀), p₀)` gives the all-time model for arbitrary initial
data. Prove completeness for this Hamiltonian before invoking the all-time
flow interface. The comparison with SR-D1 goes through SR-D4.

*Status.* Proved in
[`SpecialRelativity/Hamiltonian.lean`](../ProjectAinos/SpecialRelativity/Hamiltonian.lean)
for `m ≠ 0`; the comparison with SR-D1 is not.

### Massive and massless shells

**Target SR-D5 [A*,C].** Define the positive-energy shell for `m≥0` by

$$
\mathcal H_m^+=\{p\ne0:g(p,p)=-m^2,\ p^0>0\}.
$$

For `m>0`, its graph is `p⁰=sqrt(m²+‖p‖²)` over all spatial momenta.
For `m=0`, the graph is over nonzero spatial momenta. Construct the smooth
manifold and its inherited C∞ scheme on these domains, and prove the
orthochronous Lorentz action is smooth. The cone vertex is singular and
does not represent a physical zero-energy massless particle.

*Status.* Proved in
[`SpecialRelativity/FutureShell.lean`](../ProjectAinos/SpecialRelativity/FutureShell.lean):
the shell is the graph of the energy over an open set of the space momenta,
`FutureShell.scheme` is the C∞ scheme of that open set, and the Lorentz group
acts smoothly in the chart. The automorphisms of the scheme are not
constructed.

**Target SR-D6 [A*,B,C].** A massless particle uses an auxiliary positive
one-dimensional field `e`, with action

$$
S[x,e]=\frac12\int_a^b
\left(e^{-1}g(\dot x,\dot x)-e m^2\right)ds.
$$

Varying `e` yields `g(ẋ,ẋ)+e²m²=0`; varying `x` yields constancy of
`e⁻¹ẋ` in Minkowski coordinates. Require nonzero velocity for the massless
physical interpretation. For `m>0`, eliminating `e=sqrt(-g(ẋ,ẋ))/m`
recovers the massive action on its timelike domain. For `m=0`, it yields
null motion without normalizing a null vector by its zero proper speed.
The transformation of `e` under parameter changes is part of the action's
invariance theorem. These are new targets, not properties of the existing
total definition `fourVelocity` at a null vector.

*Status.* Proved in
[`SpecialRelativity/Einbein.lean`](../ProjectAinos/SpecialRelativity/Einbein.lean)
for `C²` pairs `(x, e)` with `e > 0` on `[a, b]`.

**Target SR-D8 [A].** On the canonical phase space of an event `x` and its
momentum covector `p`, the ideal `I = (g⁻¹(p,p) + m²)` is coisotropic. The
momenta `p_μ` and the orbital charges `x_μ p_ν − x_ν p_μ` have zero bracket
with its generator, so they lie in the normalizer `N(I)`, and their classes
in the reduced ring `N(I)/I` satisfy the relations of SR-C6. For `m > 0` and
the future sheet, take the ideal generated by `p₀ + √(m² + ‖𝐩‖²)`. After the
canonical change of variables `Q⁰ = x⁰`, `𝐐 = 𝐱 − x⁰ ∂E/∂𝐩`,
`P₀ = p₀ + E(𝐩)`, `𝐏 = 𝐩` with `E = √(m² + ‖𝐩‖²)`, this generator is a
momentum co-ordinate. Then `CyclicReduction.canonicalReductionHom_bijective`
identifies the reduced ring with the phase space of the initial data
`(𝐐, 𝐏)`, as a Poisson C∞-ring. The proof has the shape of
`TwoBody.reducedMassHom_bijective`: an explicit isomorphism of Poisson
C∞-rings, then the general theorem. The quotient ring and the smooth shell
of SR-D5 are compared by a separate theorem.

*Status.* Proved in
[`SpecialRelativity/MassShellReduction.lean`](../ProjectAinos/SpecialRelativity/MassShellReduction.lean):
the quadratic ideal for both conventions, the future sheet and its reduction
for `(−+++)` and `m ≠ 0`. The comparison with the smooth shell is not.

## Distributions, collisions and conservation

### Invariant measure and particle distributions

**Target SR-M1 [B,C].** Construct a positive measure on the future shell
whose coordinate expression is

$$
d\mu_m(p)=\frac{d^d\mathbf p}{p^0}.
$$

For the massless shell the domain omits the origin. Fix this normalization
explicitly; conventions using `1/(2p⁰)` differ by a constant. Prove invariance
under orthochronous Lorentz transformations, which preserve this future shell,
through a change-of-variables theorem, with spatial Jacobian
`|det Dp'|=p'⁰/p⁰`, or through the corresponding level-set volume form.
Neither a symbolic Jacobian identity nor the shell equation alone supplies
the measure-theoretic conclusion.

*Status.* Proved in
[`SpecialRelativity/ShellMeasure.lean`](../ProjectAinos/SpecialRelativity/ShellMeasure.lean)
by the formula for the change of variables, for every mass and every
orthochronous transformation.

**Target SR-M2 [B,C,P].** A distribution is a nonnegative measurable scalar
on the chosen shell bundle. Given a spacelike hypersurface with future unit
normal `n`, define the number flux by

$$
N_\Sigma=\int_\Sigma\int_{\mathcal H_m^+}
f(x,p)\,[-g(p,n)]\,d\mu_m(p)\,d\Sigma.
$$

Require measurability and integrability before proving invariance under
jointly transformed data. Equality of fluxes through different hypersurfaces
additionally needs a transport equation and boundary-flux conditions.
Independent spatial and momentum volume factors must not each be declared
Lorentz invariant. This is the entry point for later relativistic kinetic
theory; no equilibrium distribution is selected by SR kinematics.

*Status.* Proved in
[`SpecialRelativity/NumberFlux.lean`](../ProjectAinos/SpecialRelativity/NumberFlux.lean)
for a surface measure on the events and a field of normals, which are given;
the two are constructed for the hyperplanes of the co-ordinates.

### Decays and two-body constraints

**Target SR-C1 [A*].** For future causal nonzero momenta, prove the reverse
Cauchy–Schwarz inequality and the invariant-mass triangle inequality for
their sum. Identify the degenerate case in which parallel null momenta
have a null sum. A center-of-momentum observer exists for a timelike total
momentum `P`, with `u=P/sqrt(-g(P,P))`; it does not exist for a null total.

*Status.* Proved in
[`SmoothGeometry/Minkowski/ReverseCauchySchwarz.lean`](../ProjectAinos/SmoothGeometry/Minkowski/ReverseCauchySchwarz.lean)
and
[`SpecialRelativity/InvariantMass.lean`](../ProjectAinos/SpecialRelativity/InvariantMass.lean).

**Target SR-C2 [A*].** A two-body decay has parent rest mass `M>0`, daughter
masses `m₁,m₂≥0`, future shell conditions and `P=p₁+p₂`. In the parent rest
frame, prove

$$
E_1=\frac{M^2+m_1^2-m_2^2}{2M},\qquad
E_2=\frac{M^2+m_2^2-m_1^2}{2M},\qquad
|\mathbf p_1|=|\mathbf p_2|
=\frac{\sqrt{\lambda(M^2,m_1^2,m_2^2)}}{2M},
$$

where `λ(a,b,c)=a²+b²+c²−2ab−2ac−2bc`. For `M>m₁+m₂`, every unit spatial
direction supplies an allowed configuration. At threshold, zero spatial
momentum is admissible when both daughter masses are positive. If one daughter
is massless, the equality case would give that daughter zero energy and is
excluded by the shell definition. This distinguishes necessary algebraic
constraints from physical nonzero-particle existence.

*Status.* Proved in
[`SpecialRelativity/Decay.lean`](../ProjectAinos/SpecialRelativity/Decay.lean).

**Target SR-C3 [A*].** For elastic two-body scattering, label incoming momenta
`p₁,p₂` and outgoing momenta `p₃,p₄`, impose their future shells and
`p₁+p₂=p₃+p₄`. Use the timelike total momentum to construct the
center-of-momentum frame and parametrize outgoing directions. Define

$$
s=-g(p_1+p_2,p_1+p_2),\qquad
t=-g(p_1-p_3,p_1-p_3),\qquad
u=-g(p_1-p_4,p_1-p_4).
$$

Prove `s+t+u=Σmᵢ²`. Lab-frame formulas follow by the
already constructed boosts. The choice of outgoing angle or interaction law
is not inferred from these conservation identities.

*Status.* Proved in
[`SpecialRelativity/ElasticScattering.lean`](../ProjectAinos/SpecialRelativity/ElasticScattering.lean).
For a target at rest the invariants `s` and `t` are given in terms of the
energies; the angles in that frame are not computed.

### Cross-sections and event rates

**Target SR-C4 [B,C,P].** Construct the regular part of constrained
multi-particle phase space and its measure from product shell measures and
the total-momentum constraint. Use a coarea or distributional construction
with stated hypotheses; thresholds where the constraint map loses rank
require a separate treatment.

For two incoming particles define the invariant flux factor

$$
\mathcal F=\sqrt{g(p_1,p_2)^2-m_1^2m_2^2}.
$$

Given a nonnegative Lorentz-scalar transition weight `W` and a compatible
normalization of final-state phase space, one may define a rate model with
`dσ=W dΠ/(4ℱ)` where `ℱ>0`. Prove its covariance from the hypotheses.
This is a conditional definition of a cross-section, not a derivation of
`W` from relativity. The often used flux speed `ℱ/(E₁E₂)` is not identified
with the speed of one observer measured by another; those concepts have
different domains and bounds.

*Status.* The flux factor, the invariance of the product of two shell
measures and the covariance of the cross-section from its two hypotheses are
proved in
[`SpecialRelativity/CrossSection.lean`](../ProjectAinos/SpecialRelativity/CrossSection.lean).
The measure on the constrained final states is not constructed.

### Angular momentum and the center of energy

**Target SR-C5 [A*,B].** For a finite collection of free worldlines sampled
at a common inertial time, define total momentum and orbital angular momentum

$$
P^\mu=\sum_a p_a^\mu,\qquad
J^{\mu\nu}=\sum_a(x_a^\mu p_a^\nu-x_a^\nu p_a^\mu).
$$

Derive conservation from the free equations, and covariance under Lorentz
maps. A transformed common-time slice generally samples different events on
the worldlines. For the free system, use conservation of each worldline's
momentum and orbital charge to justify resampling on the new observer's slice.
Shifting the coordinate origin by `a` gives `J' = J−a∧P`; thus orbital
angular momentum depends on an origin although its conservation does not.
For local interaction events, impose the relevant momentum conservation and
matching conditions explicitly. For extended matter or fields, the missing
contribution is an integral of stress-energy, developed in the ED plan.

With positive total energy $E$, define the spatial center
$\mathbf X=\sum_a E_a\mathbf x_a/E$. Constancy of $J^{0i}$ implies
$d\mathbf X/dt=\mathbf P/E$, where $\mathbf P$ is the spatial part of the
total four-momentum. This energy-weighted center replaces the nonrelativistic
mass-weighted center; it is observer dependent. A universal rigid-body
interpretation or Lorentz-covariant spatial center is not assumed.

*Status.* Proved in
[`SpecialRelativity/OrbitalCharges.lean`](../ProjectAinos/SpecialRelativity/OrbitalCharges.lean).
The moment is a function of two covectors, and a shift of the events by `c`
adds `c ∧ P`.

**Target SR-C6 [A,A*].** With the canonical Poisson API of the shared
algebra (`PhaseSpace.canonical`, `IsPoissonHom`), represent translations and
Lorentz transformations by momentum functions and prove their brackets on
canonical generators. Compare these functions with the action's Noether
boundary terms. This is the Poincaré algebra of classical orbital charges;
intrinsic spin and quantum representations are later extensions.

*Status.* The brackets are proved in
[`SmoothAlgebra/Poisson/OrbitalCharge.lean`](../ProjectAinos/SmoothAlgebra/Poisson/OrbitalCharge.lean)
for every symmetric matrix and in
[`SpecialRelativity/PoincareAlgebra.lean`](../ProjectAinos/SpecialRelativity/PoincareAlgebra.lean)
for the Minkowski metric. The comparison with the Noether boundary terms is
`kineticMomentum_lorentzGenerator` in
[`SpecialRelativity/OrbitalCharges.lean`](../ProjectAinos/SpecialRelativity/OrbitalCharges.lean):
the momentum covector applied to an infinitesimal Lorentz transformation is
the orbital moment.

<a id="landau-lifshitz-correspondence"></a>

## Landau–Lifshitz correspondence

Numbers follow Volume 2, fourth revised English edition. Topic labels below
are descriptive summaries, not a transcription of the book's headings.
Each row specifies a formalization target and its premises. “Partial” means
that the cited building blocks exist, not that the complete textbook section
is proved. The [publisher entry](https://shop.elsevier.com/books/the-classical-theory-of-fields/landau/978-0-08-025072-4)
fixes the edition; the [book preview](https://books.google.com/books/about/The_Classical_Theory_of_Fields.html?id=QIxD3Z82AagC)
supports the numbering. Page numbers vary between reprints.

| § | Topic and formal target | Essential hypotheses | Tier and dependency | Baseline status |
| ---: | --- | --- | --- | --- |
| 1 | Finite signal speed: causal order and covariance of an admissible propagation relation | Chosen future cone; containment of the physical signal relation in it is a premise | A*, P; SR-F3–F4 | Causal order implemented; physical propagation model remains a target |
| 2 | Invariant intervals and causal classification of event displacements | Affine displacement; explicit Lorentz convention | A*; SR-F3 | Implemented by `intervalSq`, causal predicates and Lorentz invariance |
| 3 | Proper-time integral, invariance, dilation and inertial maximality | Local C¹ regularity on a compact segment; timelike/future conditions for clock interpretation | B; SR-K3–K4 | Integral, invariance and dilation implemented; maximality target |
| 4 | Lorentz maps, proper/orthochronous subgroups and boosts | Subluminal boost parameter; explicit convention | A*, B; SR-F3, SR-K1–K2 | Core maps and boosts implemented; factorization/rotation extension target |
| 5 | Relative velocity, subluminality and collinear composition | Future unit observers or velocity-ball elements | A*, B; SR-F4, SR-K1 | Implemented; noncollinear composition retained as a group action |
| 6 | Four-vectors, covectors, tensors and invariant contractions | Specified variance; invertible Lorentz action for mixed tensors | A*, C; SR-F2–F4 and shared tensor APIs | Native operations implemented; universal C∞ cotangent comparison target |
| 7 | Four-velocity, acceleration orthogonality and massive/null distinction | Timelike differentiable curve for normalization; C² for acceleration | A*, B; SR-K3, SR-D5–D6 | Unit four-velocity implemented; systematic acceleration and massless package targets |
| 8 | Massive variational principle, free motion and parameter degeneracy | C² path, `a<b`, timelike reference jets; `m>0` for inertial-motion conclusion | A, B, P; SR-D1–D2, SR-D8 | Actual action and stationary/EL equivalence implemented; full SR dynamics and the constraint form SR-D8 are targets |
| 9 | Observer energy/momentum, mass shell, coordinate-time Hamiltonian and Newtonian expansion | Future massive momentum; fixed observer; `m>0`; compact velocity bound for limit | A, A*, B; SR-D3–D5, SR-D7, SR-K5 | Momentum covector implemented; complete energy/Hamiltonian/limit API targets; SR-D7 needs only the shared Poisson API |
| 10 | Covariance of shell distributions and number flux | Nonnegative measurable distribution; spacelike slice; integrability | B, C; SR-M1–M2 | Target |
| 11 | Two-body decay energies, thresholds and frame conversion | Parent `M>0`; daughter future shells; conservation; nonzero daughter energies | A*; SR-C1–C2 | Target |
| 12 | Invariant phase-space rate and cross-section construction | Regular constraint locus; nonzero incoming flux; scalar transition weight | B, C, P; SR-M1, SR-C4 | Conditional target; no interaction weight is supplied by SR |
| 13 | Elastic two-body kinematics and invariant relations | Future mass shells; timelike total momentum; conservation | A*; SR-C1–C3 | Target |
| 14 | Orbital Lorentz charges and center-of-energy motion | Finite isolated free system or explicit event-balance premises; positive total energy | A, A*, B; SR-C5–C6 | Target; the Poisson prerequisite of SR-C6 exists; field contributions belong to ED |

Chapter I is §§1–7 and Chapter II is §§8–14. The ED manuscript owns §§15–80;
the GR manuscript owns §§81–119. Their curved Maxwell and gravitational
particle specializations may cite SR results, while the section ledger keeps
one primary owner for each textbook section.

## Towards Lean

### Architecture and proposed interfaces

The existing public types `Spacetime`, `FourVector`, `FourCovector`,
`Velocity d`, `Observer d`, `LorentzGroup d`, `PoincareGroup d`,
`TimelikeSegment`, `freeAction` and `kineticMomentum` remain the integration
points. New modules should add observer measurements, mass shells, measures
and conservation laws around these definitions. No new field named
“stationarity implies free motion” belongs inside a particle data structure:
the implication is a theorem of the actual action.

Proposed interfaces have the following responsibilities:

| Proposed interface | Data and public contract |
| --- | --- |
| `ParticleMomentum` / `MassShell` | Mass, future nonzero momentum, shell predicate; observer energy and spatial momentum; massive and massless domains distinguished |
| `CoordinateTimeDynamics` | Spatial velocity/momentum equivalence for positive mass, Hamiltonian and comparison to the covariant action |
| `MassShellMeasure` | Chosen measure normalization, chart formula and Lorentz pushforward equality |
| `Distribution` | Measurable nonnegative density and integrability hypotheses; flux through an explicitly supplied hypersurface |
| `CollisionKinematics` | Finite incoming/outgoing particle families, shell conditions and a separate conservation predicate |
| `OrbitalCharges` | Origin-dependent angular momentum, observer-dependent center of energy and proved transformation laws |

Names in this table are proposals, not declarations available at the baseline.
The public mathematical contracts take priority over a premature choice of
Lean structure fields. The algebraic shell predicate and smooth shell manifold
must be related by a comparison theorem rather than being silently identified.

```mermaid
flowchart TD
  algebra["SmoothAlgebra: C∞ operations, morphisms, localizations"]
  schemes["SmoothGeometry: real spectra, sheaves, schemes, manifolds"]
  lorentz["Shared Lorentz geometry: cones, observers, tensors, forms"]
  variational["Variational / Mechanics: actual first variation"]
  kinematics["SR kinematics: boosts, velocities, proper time"]
  particles["SR particles: action, momentum, mass shells"]
  measures["Shell measures and distributions"]
  collisions["Decay, scattering constraints, orbital charges"]
  ed["Electrodynamics: charged motion, fields, stress-energy"]
  gr["General Relativity: curved motion and dynamical metric"]
  algebra --> schemes
  schemes --> lorentz
  schemes --> variational
  lorentz --> kinematics
  kinematics --> particles
  variational --> particles
  particles --> measures
  particles --> collisions
  measures --> collisions
  particles --> ed
  lorentz --> ed
  particles --> gr
  lorentz --> gr
```

This is a subsystem dependency diagram, not a claim that every displayed
edge is a direct Lean import. The reusable geometric and variational cores
must remain independent of project physics. Current boundaries are enforced
by [`checks/CoreImports.lean`](../checks/CoreImports.lean).

### Analytic interfaces and proof order

| Interface | Required statement | Current use and remaining work |
| --- | --- | --- |
| SR-I1: compact curve calculus | Local C¹/C² regularity, chain rule, interval substitution and integration by parts | Used by existing proper-time and free-action theorems; reuse their actual hypotheses |
| SR-I2: localized variations | Small fixed-endpoint perturbations remain in an open timelike jet domain; actual action differentiation and fundamental lemma | Supplied by `Mechanics.OpenDomain` for the present flat model |
| SR-I3: convexity and clock comparison | Reverse Cauchy–Schwarz, integral inequality and continuous equality case | New proof targets for inertial maximality |
| SR-I4: shell change of variables | Jacobians, integration on smooth level sets and pushforward equality | `Scattering.crossSection_apply` is a proof model. Shell measures and collision-locus change of variables remain SR targets |
| SR-I5: asymptotic estimates | Uniform Taylor remainders on a compact velocity range, with explicit `c` domain | Instantiate `Variational.exists_second_order_bound` for the energy expansion. Trajectory estimates require a separate stability argument |
| SR-I6: generalized coefficients | Cotangent comparison and extension of smooth families to nilpotent coefficient algebras | Research stage; no real-coefficient theorem is promoted without this bridge |

Standard mathlib results should discharge these interfaces where available
in the pinned dependency. A missing substantial theorem may be passed as a
named hypothesis for a conditional theorem, with that dependency visible in
the ledger. It must not be introduced by `axiom`, nor hidden in a structure
whose only role is to assert the desired conclusion.

## Milestones

1. **SR0 — baseline and comparisons.** Preserve existing geometry, clock and
   action APIs. Add consumer examples connecting `kineticMomentum`, metric
   duality and normalized four-velocity. Acceptance: both signatures agree
   on causal classification and clocks; the physics wrapper remains `(-+++)`.
   Review and ratify the proposed shared interfaces with the ED and GR
   consumers before committing to new public APIs. This manuscript records
   the proposal; completing its Markdown does not complete that review gate.
2. **SR1 — free massive dynamics.** First derive constant normalized momentum
   from SR-D1 and prove the observer-energy identities. Complete SR-D2 with
   acceleration orthogonality and the velocity Hessian's radial kernel.
   Develop SR-D7 on all momenta, then connect it to the open velocity ball in
   SR-D4. Use a nonzero boosted particle, a nonlinear regular
   reparametrization, and the spatial Legendre inverse as checks.
3. **SR2 — shells and massless motion.** Construct smooth positive shells and
   the auxiliary-field variational model. Acceptance: massive rest momentum,
   a nonzero null momentum and exclusion of the null cone vertex; massive
   elimination reproduces the existing action. Prove SR-D8 for the massive
   future sheet.
4. **SR3 — algebra of finite reactions.** Prove invariant-mass inequalities,
   two-body decay formulas and elastic collision identities. Acceptance:
   unequal masses, threshold, forbidden threshold with a massless daughter,
   and null total momentum are distinguished explicitly.
5. **SR4 — measures and distributions.** Construct invariant shell measure
   and flux, then regular constrained phase-space rates. Acceptance:
   boost pushforward equality is a measure theorem; rate claims disclose
   the transition-weight and regularity hypotheses.
6. **SR5 — orbital symmetry and limits.** Prove the center-of-energy theorem,
   charge transformation and compact-velocity Newtonian estimates. Prove
   SR-C6 with the shared Poisson API.
7. **SR6 — C∞ family refinement.** Implement the universal cotangent bridge
   and selected nonreduced shell/variation examples. Acceptance: native and
   algebraic tangent descriptions agree on the real smooth locus, and every
   generalized-coefficient claim records the additional proved comparison.

SR3 can proceed after the momentum definitions without waiting for shell
integration. SR4 owns analytic rate questions. SR6 enriches the foundations
without blocking the ordinary real-model particle programme.

SR-D7, SR-D8 and SR-C6 use only the shared algebra and can be done first.
A milestone is delivered as in the mechanics programme: a small number of
pull requests that each close several rows, typed examples in a check file
run by `checks/run.sh`, and a note for each observation that changes an
interface. The [completion criterion](#after-the-mechanics-programme) decides
when the volume is done.

## Evidence and proof ledger

“Implemented” means the cited declarations exist with proofs at the
proof-status baseline. “Target” is an
unimplemented theorem in the specified real model. “Conditional target”
includes a named mathematical or physical premise. “Research target” needs
a new framework or comparison. SymPy checks remain evidence rather than
Lean proof, even when they simplify exactly to zero.

| Tag | Claim or regression | Evidence at the baseline | Outstanding acceptance condition |
| --- | --- | --- | --- |
| SR-E1 | Timelike, spacelike, null and zero classification | `Examples.timelike_example`, `spacelike_example`, `lightlike_example`, `zero_causal_not_lightlike` | Retain zero/nonzero distinction in new shells |
| SR-E2 | Velocity `3/5`, Lorentz factor `5/4`, clock rate `4/5` | `Examples.beta_gamma`, `boosted_time`, `boosted_space`, `inverse_boost`, `time_dilation` | Observer-energy example uses the same signs |
| SR-E3 | Signature-independent clock and boost geometry | `Examples.same_clock_both_signs`, `same_boost_both_signs` | Physical wrappers retain an explicit convention |
| SR-E4 | Nonzero exact two-form, closedness and gauge identity | `SpecialRelativity.coordinatePotential_exteriorDerivative`, `coordinateField_nonzero`, `coordinateField_closed`, `coordinatePotential_gauge` in `FormExamples` | ED owns physical field interpretation |
| SR-E5 | Actual free-action differentiation and momentum | `SpecialRelativity.hasFDerivAt_freeLagrangian`, `free_momentum`, `free_stationary_iff` in `ParticleAction` | Derive the complete SR free-motion and energy package |
| SR-E6 | Mass normalization | Downstream `Electrodynamics.mass_shell` proves `g(mU,mU)=−m²` under timelikeness | Add an SR-owned shell theorem without an ED import |
| SR-E7 | Shell measure invariance | Target; no shell-measure theorem claimed | Lean change-of-variables proof with chosen normalization |
| SR-E8 | Decay and elastic kinematics | Target; no newly executed experiment claimed | Exact Lean examples for masses, threshold and boosted data |
| SR-E9 | Rest-energy subtraction and `c→∞` remainder | Target | Quantified uniform estimate, not a formal series alone |
| SR-E10 | Universal C∞/native tangent comparison | Research target | Prove restriction and pullback compatibility before reuse |
| SR-E11 | Shared prerequisites supplied by the mechanics programme | [Canonical algebra](../checks/CanonicalAPI.lean), [reduction](../checks/ReductionAPI.lean), [Hamiltonian flow](../checks/HamiltonianFlowAPI.lean) and [scattering measures](../checks/ScatteringAPI.lean) | SR-owned consumer examples for SR-D7, SR-D8 and SR-C6; an invariant shell measure |

The existing experiment package contains
[`verify_electrodynamics.py`](../experiments/ainos_experiments/verify_electrodynamics.py)
and [`verify_lorentz_geometry.py`](../experiments/ainos_experiments/verify_lorentz_geometry.py).
They check related field-invariant and coordinate-geometry identities; they
are not a completed SR collision or distribution experiment suite. Future
short SR checks should use exact SymPy arithmetic first, with parameters,
tolerances and seeds recorded if numerical calculations become necessary.

Future Lean changes require the warning-free library build, root-import
check, relevant default-option consumer checks and transitive axiom audit:

```sh
lake build --wfail ProjectAinos
lake exe mk_all --check --lib ProjectAinos
lake env lean -DwarningAsError=true --run checks/CoreImports.lean
lake env lean -DwarningAsError=true checks/SpecialRelativityAPI.lean
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
```

The axiom allowlist is `propext`, `Classical.choice`, `Quot.sound`. Physical
premises remain hypotheses or predicates. Experiment checks use the separate
non-required workflow; documentation generation follows [docs/build.md](build.md).
For this design deliverable, acceptance additionally requires all fourteen
section rows, valid crosslinks, clear status labels and agreement with the
other two manuscripts' conventions and dependency boundaries.

## References

- L. D. Landau and E. M. Lifshitz, *The Classical Theory of Fields*, fourth
  revised English edition, Course of Theoretical Physics, vol. 2, translated
  by Morton Hamermesh, Chapters I–II, §§1–14.
  [Publisher](https://shop.elsevier.com/books/the-classical-theory-of-fields/landau/978-0-08-025072-4)
  · [Section-number preview, ISBN 9780750627689](https://books.google.com/books/about/The_Classical_Theory_of_Fields.html?id=QIxD3Z82AagC).
  Section numbers are the correspondence keys; reprint page numbers are not.
- D. Joyce, *Algebraic Geometry over C∞-rings*, Memoirs of the AMS **260**
  (2019), no. 1256; [arXiv:1001.0023v7](https://arxiv.org/abs/1001.0023v7),
  §§2–4 and §§5.2, 5.6. Completeness and cotangent comparisons require their
  stated hypotheses; this reference does not itself constitute a Lean proof.
- [C∞ mechanics research plan](cinfty-mechanics.md): tier conventions,
  variational identities, constrained Hamiltonian systems and proof ledger.
  [Mechanics formalization notes](mechanics-notes.md): M37 and M74 on domains
  that are not all of `ℝⁿ`, M66 on hypotheses that need an instance, M70–M72
  on quotients and reduction.
- [Shared smooth geometry](smooth-geometry.md) and
  [formalization notes](smooth-geometry-notes.md): constructed spectra,
  manifold schemes, native bundles and the outstanding algebraic comparisons.
- [SR implementation guide](special-relativity.md),
  [ED implementation guide](electrodynamics.md), and
  [GR implementation guide](general-relativity.md): actual public APIs and
  the existing flat/curved comparison results at the recorded baseline.

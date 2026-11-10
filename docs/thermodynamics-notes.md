# Thermodynamics Formalization Notes

These notes record mathematical distinctions and modeling decisions made explicit by the Lean development. Each entry gives the argument, its effect on the public interface, and the proof status. A known theorem becoming visible in a formal interface is distinct from a new physical result.

The research roadmap remains in [README](../README.md#thermodynamics-proof-development). New observations should be added here with links to the relevant definitions and proofs; unresolved claims should be marked as such.

## T01. The empty system and thermal equilibrium

**Observation.** The empty system can serve as the identity for composition without being an ordinary member of the thermal-equilibrium relation.

Suppose raw states form a monoid with `0 • x = 0`. If a relation `R` obeys

\[
R((1-t)\,x,t\,x)\qquad(0\le t\le1)
\]

for every raw state, then setting `t = 0` gives `R(x, 0)`. Symmetry and transitivity imply `R(x, y)` for every pair of states. Thus an endpoint-inclusive raw relation, together with the zeroth law on that same type, loses the distinction between isotherms.

**Interface decision.** Adiabatic splitting retains zero endpoints. The raw scaled-copy *thermal-equilibrium* premise uses `0 < t < 1`, so both systems have positive scale. `ThermalJoin.RealizesThermalEquilibrium` explicitly connects this relation to reversible contact between states in specified coordinate domains.

The original T2 includes endpoints in a typed adiabatic splitting equation. The collapse above concerns extending thermal equilibrium to the empty element of our single raw-state type. [Lieb–Yngvason, §IV, T2–T3 and Theorem 4.1](https://arxiv.org/html/cond-mat/9708200v2)

**Proof status.** `thermal_relation_universal_of_endpoint_split` proves the collapse through the empty state under the hypotheses above. `ScaledCopyThermalEquilibrium.self_scale` and `.scale_iff` prove equilibrium with positive scaled copies and invariance under independent positive scaling. The raw relation's compatibility with each thermal join remains an explicit premise. [Definitions](../ProjectAInos/Thermodynamics/PhysicalComparison.lean) · [Thermal equilibrium proofs](../ProjectAInos/Thermodynamics/ThermalEquilibrium.lean)

## T02. Entropy order requires a conserved sector

**Observation.** Entropy monotonicity and a complete entropy criterion for accessibility have different hypotheses.

Let `V` be the completed state space, `P` its process cone, `W = span ℝ P`, and `π : V → V/W` the quotient map. Stability A6, a nonzero process direction, and exchange comparison give a real entropy coordinate on `W`. For an extension `S` to `V`, the complete criterion is

\[
\pi(\iota x)=\pi(\iota y)
\quad\Longrightarrow\quad
(x\le y\;\Longleftrightarrow\;S(\iota x)\le S(\iota y)).
\]

The sector hypothesis cannot be dropped. In the entropy–amount model, `(s,n) ≤ (s',n')` means `n = n'` and `s ≤ s'`. Increasing the entropy coordinate while changing the conserved amount does not produce an accessible process.

**Interface decision.** Totality is asserted on `W`, while `V` retains a partial order. The construction of `V/W`, its exact sequence, and its universal property require no comparison hypothesis. Once the entropy coordinate on `W` is fixed, all extensions have the form `S₀ + φ ∘ π`. Their ambiguity is precisely a conserved linear quantity.

**Proof status.** `EntropyExtension.state_le_iff` includes sector equality in its type. `different_amounts_incomparable` supplies a concrete counterexample. `conservation_exact` and `EntropyExtension.equivConserved` establish the quotient and extension classification. [Entropy](../ProjectAInos/Thermodynamics/Entropy.lean) · [Conservation](../ProjectAInos/Thermodynamics/Conservation.lean) · [Sector model](../ProjectAInos/Thermodynamics/SectorModel.lean)

## T03. The reference cutoff measures relative entropy

**Observation.** Normalizing the difference between two reference states fixes an entropy unit. It does not set the entropy of the first reference state to zero.

For matched-sector states and `S(ιx₁) − S(ιx₀) = 1`, the reference cutoff is

\[
\sup\{\lambda\in\mathbb R:
  (1-\lambda)x_0+\lambda x_1\preceq x\}
=S(\iota x)-S(\iota x_0).
\]

Here a negative coefficient is interpreted by moving the corresponding positive amount to the other side of the accessibility relation. Writing `a⁺ = max(a,0)` and `a⁻ = max(-a,0)`, the actual state-level inequality is

\[
(1-\lambda)^+x_0+\lambda^+x_1
\preceq x+(1-\lambda)^-x_0+\lambda^-x_1.
\]

**Interface decision.** `signedReferenceLE` uses only nonnegative scalar multiplication on physical states and accepts every real cutoff parameter, including `λ < 0` and `λ > 1`. No physical state is multiplied by a negative amount. The resulting entropy difference is independent of the chosen extension because both states lie in the same conserved sector.

**Proof status.** `signedReferenceLE_iff_entropy_le` identifies the entire cutoff set as a real lower interval. `reference_cutoff_eq_relative_entropy` then computes its supremum. [Cutoff proofs](../ProjectAInos/Thermodynamics/Cutoff.lean)

## T04. Splitting becomes an algebraic identity only after quotienting

**Observation.** A scaled system and two separate scaled copies have different raw descriptions. Their adiabatic equivalence is physical input.

Before quotienting, the composite-state type has addition and a multiplicative scalar action, expressed by `AddCommMonoid` and `DistribMulAction ℝ≥0`. The identity `(a+b) • x = a • x + b • x` is obtained on adiabatic classes from the splitting premise. This is the step that supplies the full `Module ℝ≥0` structure.

**Interface decision.** Structural identifications and mutual accessibility use separate quotients. Similarly, cancellation is proved from stability A6 before it is installed as an ordered algebraic instance. This keeps the physical role of splitting and stability visible in the dependency graph.

**Proof status.** `splitting_of_normalized` extends the usual positive normalized split to homogeneous splits, with zero cases supplied by the empty system. `Accessibility.StateSpace` carries the resulting semimodule, and `Stability.le_of_add_le_add_right` proves spectator cancellation. [Physical states](../ProjectAInos/Thermodynamics/Physical.lean) · [Cancellation](../ProjectAInos/Thermodynamics/Cancellation.lean)

## T05. Infinite reaction costs distinguish two different failures

**Observation.** A direct cost is an infimum of calibrated entropy differences. An unavailable transition has cost `+∞`; an unbounded family of available entropy decreases can have infimum `−∞`. These cases have different meanings and must survive the early definitions.

**Interface decision.** Direct, finite-chain, and catalytic costs use `EReal`. A chain initially requires each edge cost to be less than `+∞`, which still allows `−∞`. Nonnegative cycle costs follow from composition and entropy monotonicity within a label. The no-sinks premise supplies reverse connectivity; together these facts exclude `−∞` before selecting real entropy constants by Hahn–Banach. Unreachable differences can still have cost `+∞`.

**Proof status.** `calibratedDirectCost_cycle_nonneg` proves cycle consistency from raw transitions. `calibrated_connected_iff_actual` identifies finite-above connectivity with actual chains and ancillary systems. `exists_weak_entropy_from_raw_states` returns an additive, extensive, monotone corrected entropy under explicit raw-state premises. In the equality-only model with cancellative label composition, distinct conserved labels remain at cost `+∞` even after adding catalysts. [Cycle proofs](../ProjectAInos/Thermodynamics/ReactionCycles.lean) · [Weak entropy theorem](../ProjectAInos/Thermodynamics/PhysicalReactions.lean) · [Infinite-cost model](../ProjectAInos/Thermodynamics/ReactionModels.lean)

## T06. A normalized pressure form does not fix the supporting side

**Observation.** A supporting hyperplane is unchanged when its defining nonzero linear form is multiplied by a nonzero constant. Uniqueness of the plane therefore concerns kernels. It cannot be expressed as equality of arbitrary chosen normals.

The finite-slope pressure form is normalized as

\[
f_X(\delta U,\delta V)=\delta U+\sum_i P_i(X)\,\delta V_i.
\]

Its energy coefficient is one, but the forward sector may initially lie on either side. The common orientation of sectors is a further theorem to prove, not part of this normalization.

**Interface decision.** S2 supplies a supporting choice of `f_X` or `−f_X`, uniqueness of the supporting kernel, and local Lipschitz continuity of the pressure field. S3 concerns path-connectedness of the boundary *inside the open equilibrium domain*. Including the exterior boundary of that domain, or replacing path-connectedness with connectedness without a proof, would change the hypothesis. [Lieb–Yngvason, §III, S2–S3](https://arxiv.org/html/cond-mat/9708200v2)

**Proof status.** `SimpleSystem.forwardSector_interior_nonempty` proves nonempty interior using irreversibility, finite-slope unique support, and the earlier collinear accessibility lemma. Support inheritance at relative-boundary points, common energy orientation, and a differentiable boundary graph are proved. Its derivative is the negative pressure form. Grönwall's inequality gives local uniqueness; S3 propagates boundary reversibility, and convex segment crossing gives `SimpleSystem.comparison_of_mem`. Strict forward sectors are nested, and strict reference strips are open. Reflection preserves every simple-system premise, so none of these final results assumes a preferred energy orientation. [Energy orientation](../ProjectAInos/Thermodynamics/EnergyOrientation.lean) · [Energy reflection](../ProjectAInos/Thermodynamics/EnergyReflection.lean) · [Boundary derivative](../ProjectAInos/Thermodynamics/BoundaryDifferentiability.lean) · [Local uniqueness](../ProjectAInos/Thermodynamics/AdiabatUniqueness.lean) · [Simple-system comparison](../ProjectAInos/Thermodynamics/SimpleComparison.lean)

## T07. Thermal equilibrium can be expressed before entropy is differentiable

**Observation.** Concavity alone need not give a unique energy derivative. At an interior energy, it gives a nonempty interval of supporting slopes,

\[
\partial^+ s(U)=[s'_+(U),s'_-(U)].
\]

For two concave energy functions on open convex domains, an allocation maximizes `s₁(u) + s₂(E − u)` exactly when the two supporting-slope intervals intersect. A common slope bounds both entropy changes, which cancel at fixed total energy. Conversely, the one-sided derivatives at a maximum give the cross inequalities needed for the intervals to intersect.

**Interface decision.** The early thermal criterion uses an interval of slopes rather than assuming a differentiable entropy or a unique inverse temperature. Its physical specialization currently compares two copies of the same simple system, with a common entropy normalization. Extending this to different systems requires the separate calibration argument.

**Proof status.** `supportingSlopes_eq_Icc` identifies the interval, and `isMaxOn_add_reflection_iff_inter_supportingSlopes` proves the generic maximum criterion. `ThermalFamily.thermal_iff_entropySlopes_inter` connects it to actual thermal equilibrium through the entropy representation and thermal join. These proofs do not establish the full location-of-isotherms dichotomy or existence of calibrators in every case. [Supporting slopes](../ProjectAInos/Thermodynamics/SupportingSlopes.lean) · [Entropy maximization](../ProjectAInos/Thermodynamics/ThermalMaximizers.lean) · [Thermal criterion](../ProjectAInos/Thermodynamics/ThermalSlopes.lean) · [Calibrator branch](../ProjectAInos/Thermodynamics/CalibratorExistence.lean)

## Scope of the current physical derivation

Simple-system comparison is now derived from the geometric premises. The algebraic entropy theorem still assumes exchange comparison: completing its physical derivation requires heterogeneous-product calibration and coherent thermal joins. In particular, thermal compatibility of an equilibrated joined state with its components must be justified; adiabatic equivalence alone is not a premise allowing transport of the thermal relation. Likewise, the weak reaction entropy theorem takes calibrated additive entropy and its monotonicity within each label as inputs. Its existence theorem does not by itself establish those physical calibration premises.

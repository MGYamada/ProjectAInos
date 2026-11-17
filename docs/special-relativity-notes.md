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

## SR03. The energy is an operation of the momenta, and its proofs use two relations

**Observation.** An operation of a C∞-ring is a function that is smooth on all of `ℝⁿ`. The function `s ↦ √(m² + s)` is not smooth at `s = −m²`, so the energy is not an operation applied to the element `Σ pᵢ²`. The function `w ↦ √(1 + Σ wᵢ²)` of `d` variables is smooth on all of `ℝᵈ`. Its partial derivatives are `wᵢ/√(1 + Σ wᵢ²)`, and after this one calculation every statement about the energy follows from `E² = m² + Σ πᵢ²`, `E E⁻¹ = 1` and `D E = E⁻¹ Σ πᵢ D πᵢ` by ring identities.

**Interface decision.** The shared algebra defines `relEnergy m π = m · lorentzFactor (π/m)` and `relEnergyInv m π` for a tuple `π` of elements of any C∞-ring. The hypothesis of the relations is `m ≠ 0`; for a negative `m` the element is minus the energy. The value `√(m² + Σ πᵢ²)` is stated on real numbers and for `m > 0`. The tuple is arbitrary, so the same definition gives the energy `relEnergy m (p − e a)` of a charged particle and the inertia `relEnergy m (ε p)` with `ε = 1/c`.

**Proof status.** `relEnergy_mul_self`, `relEnergy_mul_relEnergyInv`, `SmoothDerivation.apply_relEnergy`, `SmoothDerivation.apply_relEnergyInv`, `relEnergy_real` and `sum_sq_relEnergyInv_mul_lt_one` are proved. [Energy](../ProjectAinos/SmoothAlgebra/RelEnergy.lean) · [Hamiltonian](../ProjectAinos/SpecialRelativity/Hamiltonian.lean)

## SR04. The reduction is that of the future sheet, and the quadratic ideal supplies the normalizer

**Observation.** The ideal of `η⁻¹(p, p) + m²` is coisotropic, and the momenta and the Lorentz charges have zero bracket with its generator. Its zero set has two sheets, so its reduced ring is not the phase space of the initial data of one particle. The future sheet is the ideal of `p₀ + E` with `E = √(m² + Σ pᵢ²)`. The bracket of a boost charge `J₀ᵢ` with `p₀ + E` is not zero; it is `−(pᵢ/E)(p₀ + E)`, a multiple of the generator. Since `η⁻¹(p, p) + m² = (E − p₀)(p₀ + E)` and `(E − p₀) E⁻¹ = 2 − (p₀ + E) E⁻¹`, the factor `E − p₀` is invertible modulo the future sheet, and the normalizer of the quadratic ideal is contained in the normalizer of the future sheet.

**Interface decision.** The phase space of an event is `PhaseSpace (Fin (d + 1))` with the time at the index `0`, as in `MinkowskiModel d`. The new variables are indexed by `Fin d ⊕ Unit`, the form that `CyclicReduction.canonicalReductionHom_bijective` takes. The quadratic ideal is stated for both conventions. The future sheet and its reduction are stated for `(−+++)`: for `(+−−−)` the future sheet is `p₀ = E` and the space components of the covector change their sign, so the change of variables is a different one. `MassShell.reductionHom` takes `d` as an explicit argument, since the hypothesis `m ≠ 0` does not determine it.

**Proof status.** `isCoisotropic_shellIdeal`, `shellFunction_eq`, `normalizer_shellIdeal_le`, `isPoissonHom_toShellCoordinates`, `reductionHom_bijective`, `isPoissonHom_reductionHom` and `reductionHom_initialData` are proved. The comparison of the quotient ring with the shell as a manifold (SR-D5) is not. [Mass shell](../ProjectAinos/SpecialRelativity/MassShellReduction.lean)

## SR05. The contraction to the Galilei algebra is a family in a real parameter

**Observation.** With `ε = 1/c`, the energy divided by `c²` is `√(m² + ε² Σ pᵢ²)`, which is smooth for every real `ε` and equal to `m` at `ε = 0`. The boost charge `inertia · qᵢ` and the momenta satisfy `{Kᵢ, pⱼ} = δᵢⱼ · inertia`, `{Kᵢ, Kⱼ} = −ε² Mᵢⱼ` and `{Kᵢ, inertia} = ε² pᵢ` for every `ε`. The energy itself is `inertia/ε²` and has no value at `ε = 0`. The kinetic energy `Σ pᵢ²/(inertia + m)` has the value `Σ pᵢ²/2m` there, and it needs the operation `1/(√(1 + Σ wᵢ²) + 1)`, which the shared algebra does not define.

**Interface decision.** The family is indexed by a real number `ε`, and each member is a set of elements of `PhaseSpace (Fin d)`. The parameter is not adjoined as a generator, so the statement that the family is smooth in `ε` is not made. The relation with the Hamiltonian is stated as `{Kᵢ, inertia} = ε² pᵢ`. The expansion of the energy in `1/c` is the target SR-K5.

**Proof status.** `inertia_zero`, `inertia_one`, `canonical_boostCharge_p`, `canonical_boostCharge_boostCharge`, `canonical_boostCharge_inertia` and `canonical_angularMomentum_boostCharge` are proved. A member of the family for the kinetic energy is not defined. [Poincaré algebra](../ProjectAinos/SpecialRelativity/PoincareAlgebra.lean)

## SR06. In a free C∞-ring a product with a negative factor is simplified by `ring`

**Observation.** `FreeSmoothRing ι` is a subalgebra of the functions on `ι → ℝ`. For its elements, `rw [mul_neg]`, `rw [neg_mul]` and `simp` with these lemmas do not find the pattern in `x * -y`. In a file with `module`, the term `mul_neg_one x` is rejected for the goal `x * -1 = -x`, with the message that `Real.instMul`, `Real.instOne` and `Real.instNeg` were not unfolded because their definitions are not exposed. The rewrite fails in the same way for an arbitrary `Subalgebra ℝ (ℕ → ℝ)`, so it does not depend on this library. `ring` and `linear_combination` prove such goals, and `neg_zero`, `smul_neg`, `mul_sub` and `sub_eq_add_neg` rewrite as usual. In a C∞-ring `A` given by a variable all of these lemmas apply.

**Interface decision.** No instance is added. A step that moves a negation through a product of elements of a phase space is written with `ring` or `linear_combination`, and a general identity is stated for an arbitrary C∞-ring where that is possible.

**Proof status.** The proofs of `PhaseSpace.canonical_linearMomentum_linearMomentum` and of the brackets in `MassShell` are written in this way. [Linear momentum functions](../ProjectAinos/SmoothAlgebra/Poisson/LinearMomentum.lean)

## SR07. The two actions are compared through their stationary curves

**Observation.** The action of space-time `−m ∫ ds` and the action `−m ∫ √(1 − Σ vᵢ²) dt` in the time of an observer have the same value on a graph `t ↦ (t, x(t))`. Their stationarity is not the same condition by definition: the variations of the first move the time co-ordinate as well. A general route is the identity `EL(γ)·γ̇ = 0` for a Lagrangian that is homogeneous of degree one in the velocity, which gives the time component of the Euler–Lagrange covector from the space components. For the free particle both conditions have an explicit form: the first holds if and only if the unit four-velocity `γ (1, v)` is constant, the second if and only if the velocity `v` is constant.

**Interface decision.** `FreeParticle.free_stationary_graph_iff` is proved from `free_stationary_iff_fourVelocity_const` and `FreeParticle.stationary_iff_deriv_const`. No lemma on graphs or on homogeneous Lagrangians is added to the shared variational layer. The same route applies to a charged particle if both conditions are reduced to the equations with the Lorentz force. The statement is for three space dimensions, because the action of space-time is (SR01); the Lagrangian in the time of an observer and its Legendre transformation are stated for every `d`.

**Proof status.** `free_stationary_iff_inertial`, `FreeParticle.stationary_iff_deriv_const`, `FreeParticle.isTrajectory_iff_legendre` and `FreeParticle.free_stationary_graph_iff` are proved. [Free motion](../ProjectAinos/SpecialRelativity/FreeMotion.lean) · [Legendre transformation](../ProjectAinos/SpecialRelativity/SpatialLegendre.lean)

## SR08. A curve with corners is a list of pieces with matching endpoints

**Observation.** `TimelikeSegment γ a b` asks that `γ` is `C¹` near every point of the closed interval, the two ends included. A curve with a corner at a time `s` satisfies this on neither side of `s`. `properTime γ a b` is an integral of `deriv γ`, whose value at a corner is zero by convention and does not affect the integral.

**Interface decision.** The inequality for a curve with corners, `sum_properTime_le_properSpeed`, takes the pieces as separate curves `pieces i`, each a `TimelikeSegment` on `[s i, s (i + 1)]`, that agree with the curve at the times `s i`. Its left-hand side is the sum of the proper times of the pieces. It also returns that the total displacement is future causal, which the induction uses. The case of equality is stated for one piece.

**Proof status.** `TimelikeSegment.properTime_le_properSpeed`, `TimelikeSegment.properTime_eq_properSpeed_iff` and `sum_properTime_le_properSpeed` are proved. [Maximal proper time](../ProjectAinos/SpecialRelativity/MaximalProperTime.lean)

## SR09. The expansion in `1/c` uses two exact identities

**Observation.** With `s = √(1 − x)`, `1 − x/2 − s = (1 − s)²/2` and `s (1 + x/2 + x²/2) − 1 = (1 − s)² (s² + s³/2 − 1)`. For `0 ≤ x ≤ 1/4` these give `0 ≤ 1 − x/2 − √(1 − x) ≤ x²/2` and `0 ≤ 1/√(1 − x) − 1 − x/2 ≤ x²/2` without a bound on a second derivative. The remainders of the energy and of the Lagrangian have a sign: the energy is at least `m c² + ½ m v²` for `m ≥ 0`.

**Interface decision.** `Newtonian` has its own definitions with the parameter `c`, and no definition of the files with `c = 1` is changed. The hypotheses are `Σ vᵢ² ≤ V²`, `2V ≤ c` and `0 < c`, and the constants are `|m| V⁴/(2c²)`, `|m| V³/c²` and `V⁴/(2c⁴)`. The estimates are for functions of the velocity; no statement is made on the limit of a trajectory.

**Proof status.** `Newtonian.sqrt_one_sub_bounds`, `Newtonian.inv_sqrt_one_sub_bounds`, `Newtonian.abs_energy_sub_le`, `Newtonian.abs_lagrangian_sub_le`, `Newtonian.abs_momentum_sub_le` and `Newtonian.abs_clockRate_sub_le` are proved. [Expansion](../ProjectAinos/SpecialRelativity/NewtonianExpansion.lean)

## SR10. The factorization is a rotation after a boost, in the frame of the co-ordinates

**Observation.** `boost β` is a passive transformation: it brings the observer with the velocity `β` to rest (`boost_observer`). For an orthochronous `L` the vector `L⁻¹ e₀` is the velocity of the observer that `L` brings to rest, and `L · (boost β)⁻¹` then fixes the time axis `e₀`. This gives the factorization `L = R · boost β` and its uniqueness in one step each. With the other order of the factors the boost is determined by `L e₀` instead. The product of two boosts with velocities along one direction is a boost; for other velocities it is not, and the rotation that remains is the rotation part of the product.

**Interface decision.** The rotations are the stabilizer of the time axis, `rotationGroup d`, and the factor order is rotation after boost. The statements are for the observer of the co-ordinate frame; for another observer one conjugates with a boost, and this is not stated. `wignerRotation β₁ β₂` is defined as the rotation part of `boost β₁ · boost β₂`; its angle is not computed. The transformation need not be proper: a reflection of space is a rotation in this sense.

**Proof status.** `rotationPart_mul_boost`, `eq_of_mul_boost_eq`, `boostPart_eq_zero_iff`, `boostPart_boost_mul_boost`, `boost_collinear_mul` and `wignerRotation_collinear` are proved. [Factorization](../ProjectAinos/SpecialRelativity/Factorization.lean)

## SR11. Collisions are stated for momentum vectors and the quadratic form `Q`

**Observation.** The statements on the invariant mass, on decays and on collisions do not depend on the sign convention if they are written with the normalized pairing `pair` and `Q(p) = pair p p`: the mass shell is `Q(p) = m²`, and `s = Q(p₁ + p₂)`. The energy and the momentum measured by an observer are `observerEnergy` and `observerMomentum`, so the rest frame of a parent and the frame of the centre of momentum need no boost: they are the observer in the direction of the total momentum. A causal vector is in the future cone if and only if its pairing with one future timelike vector is not negative (`futureCausal_of_pair_nonneg`); this is how the constructed daughters are shown to be in the future cone.

**Interface decision.** `TwoBodyDecay` and `ElasticCollision` are structures of hypotheses on momentum vectors in `d` space dimensions; an elastic collision is two decays of the same total momentum, which gives its statements in the frame of the centre of momentum. The hypothesis that the daughters are in the future cone is separate from the mass shells, and it is used only for `m₁ + m₂ ≤ M`. At the threshold the theorem gives `pᵢ = mᵢ u`; that a daughter of mass zero then has the momentum zero is read off from it.

**Proof status.** `invariantMass_add_le`, `intervalQuadratic_add_eq_zero_iff`, `eq_centreOfMomentum`, `TwoBodyDecay.energy_first`, `TwoBodyDecay.momentum_sq_first`, `exists_twoBodyDecay`, `mandelstam_sum` and `exists_elasticCollision` are proved. The angles in the frame of a target at rest are not computed. [Invariant mass](../ProjectAinos/SpecialRelativity/InvariantMass.lean) · [Decay](../ProjectAinos/SpecialRelativity/Decay.lean) · [Collisions](../ProjectAinos/SpecialRelativity/ElasticScattering.lean)

## SR12. The finite speed of signals is a hypothesis on a relation

**Observation.** The geometry supplies the causal order and its invariance under the orthochronous Poincaré group. That a physical signal from `p` can reach `q` only if `q − p` is in the future cone is not a theorem of the geometry.

**Interface decision.** A signal is a relation `R` between events, and the premise is the predicate `IsCausalRelation R`. The consequences are stated for every such relation: the invariance of the premise, the absence of signals between events with a spacelike separation, the order in time for every observer, and the bound on the speed measured by every observer. No relation of a physical theory is asserted to satisfy the premise.

**Proof status.** `causallyPrecedes_poincare`, `IsCausalRelation.transform`, `IsCausalRelation.not_of_spacelike`, `IsCausalRelation.clock_pos` and `IsCausalRelation.restForm_le_clock_sq` are proved. [Causality](../ProjectAinos/SpecialRelativity/Causality.lean)

## SR13. The shell is a graph with one chart

**Observation.** The future shell `Q(p) = m²`, `p⁰ > 0` is the graph of `√(m² + Σ πᵢ²)` over the space momenta, and this function is smooth exactly where `m² + Σ πᵢ² > 0`. One description therefore covers both cases: the domain is all of `ℝᵈ` for `m ≠ 0` and `ℝᵈ` without the origin for `m = 0`, where the missing point is the vertex of the cone. The chart is the linear map `spaceMomentum`, so the shell is an open set of `ℝᵈ` as a manifold, and a Lorentz transformation in this chart is `π ↦ spaceMomentum (L (point m π))`. The shell is a set of momentum vectors; the ideal of the future sheet of SR04 is in the ring of functions of an event and a momentum covector, with `p₀ = −p⁰` for `(−+++)`.

**Interface decision.** The space momenta are `Fin d → ℝ` and the statements use the sum of squares (SR02). The smoothness of the graph and of the action is stated on the open domain with `ContDiffOn`. `FutureShell.scheme d m` is defined as the scheme of the open set `domainOpens d m`; no morphism of this scheme is constructed: `Manifold.schemeMap` takes a smooth map between the open sets as manifolds, and the action is proved smooth as a map on the ambient space. The comparison with the ideal is a statement on real points, through `momentumVector`, for `m > 0`.

**Proof status.** `FutureShell.chart`, `contDiffOn_point`, `mem_shell_zero_iff`, `lorentz_mem_shell`, `contDiffOn_action`, `action_mul` and `lift_futureShellFunction_eq_zero_iff` are proved. The automorphisms of the scheme are not constructed. [Future shell](../ProjectAinos/SpecialRelativity/FutureShell.lean)

## SR14. The auxiliary field is a second configuration variable

**Observation.** The Lagrangian `½ (−Q(ẋ)/e − e m²)` does not contain the derivative of `e`. In the variational setting of mechanics it is a Lagrangian on the configurations `(x, e)`, and the Euler–Lagrange covector on this product has two components: the component of `e` is the algebraic equation `Q(ẋ) = e² m²`, and the component of `x` is the derivative of `ẋ/e`. For `m > 0` the first equation gives `e = √Q(ẋ)/m`, and then `ẋ/e = m U`. For `m = 0` it says that the velocity is null, and the second equation gives `ẋ = e k` with a constant null vector `k`; the unit four-velocity, which divides by `√Q(ẋ)`, does not appear.

**Interface decision.** The domain of the Lagrangian is `e > 0`, and the theorem is for `C²` functions `x` and `e`. The comparison with the action `−m ∫ ds` has two directions with different hypotheses: a stationary pair gives a stationary curve, and a stationary curve gives a stationary pair if a `C²` function `e` with `e = √Q(ẋ)/m` on `[a, b]` is supplied. The change of the parameter is stated for the value of the Lagrangian and for the action, with `e` replaced by `(e ∘ f) f′`; the derivative of `f` is assumed not to vanish, and the pair stays in the domain when it is positive.

**Proof status.** `Einbein.stationary_iff`, `lagrangian_eliminate`, `free_stationary_of_stationary`, `stationary_of_free_stationary`, `stationary_massless_iff`, `deriv_eq_smul_of_stationary_massless` and `action_reparametrize` are proved. [Auxiliary field](../ProjectAinos/SpecialRelativity/Einbein.lean)

## SR15. The invariance of `dᵈπ/E` is proved for a boost and for a rotation

**Observation.** In the chart of the shell a Lorentz transformation is the map `π ↦ spaceMomentum (L (point m π))`, and its Jacobian is `E′/E`. For a general `L` this determinant is not a short calculation. With the factorization of SR10 it is not needed: a rotation acts by a linear map that preserves `Σ πᵢ²`, so it preserves the volume, the domain and the energy; a boost has the derivative `1 + ℓ ⊗ β`, whose determinant `1 + ℓ(β)` is `E′/E` by the identity `γ² (1 − |β|²) = 1`. The two cases compose on the domain, which carries the measure. The proof uses no property of the mass, so it covers the mass zero, where the domain omits the origin.

**Interface decision.** The measure is defined on the space momenta `Fin d → ℝ` as the Lebesgue measure restricted to the domain with the density `1/E`; the normalization `1/(2E)` differs by a constant. The invariance is the equality `Measure.map (action m L) (measure d m) = measure d m`. Two general statements carry the argument and are stated for any measure: a map that preserves a measure and a density, and a differentiable injective map whose Jacobian compensates the change of a density.

**Proof status.** `FutureShell.map_action_measure_rotation`, `map_action_measure_boost`, `map_action_measure` and `integral_comp_action` are proved. [Shell measure](../ProjectAinos/SpecialRelativity/ShellMeasure.lean)

## SR16. A hypersurface enters through its surface measure

**Observation.** The number of particles through a hypersurface is `∫ ⟨n, N⟩ dΣ`, where `N` is the number current of the distribution at each event. Its invariance under a Lorentz transformation of all the data follows from the fact that `N` is a vector, if the surface measure of the transformed hypersurface is the image of the surface measure. For a hyperplane this is how its surface measure is obtained from that of the hyperplane `x⁰ = τ`. A surface measure for a general hypersurface is not available in the library.

**Interface decision.** `numberFlux m σ n f` takes a measure `σ` on the events and a vector `n`, and `numberFlux_transform` is stated for every measure. `hyperplaneMeasure d τ` is the image of the Lebesgue measure of `ℝᵈ` on the hyperplane `x⁰ = τ`, for which the number is `∫∫ f dᵈπ dᵈx`. The integrability of `f p` on the shell is a hypothesis at every event. No statement compares the numbers through two different hypersurfaces: that needs an equation of transport for `f`.

**Proof status.** `FutureShell.numberCurrent_transform`, `numberDensity_transform`, `time_numberCurrent`, `numberFlux_transform` and `numberFlux_hyperplane` are proved. [Number flux](../ProjectAinos/SpecialRelativity/NumberFlux.lean)

## SR17. The orbital moment is a function of two covectors, and the cross-section has two hypotheses

**Observation.** The moment `x ∧ p` is a tensor with two upper indices. As the function `(α, β) ↦ α(x) β(p) − α(p) β(x)` of two covectors its transformation law is the pullback of the covectors, and it holds by definition. For two covectors the field `x ↦ α(x) β♯ − β(x) α♯` is an infinitesimal Lorentz transformation, and the momentum covector applied to it is this function: the orbital moment is the charge of Noether's theorem, and the functions of SR-C6 on the phase space are its components. For the cross-section, the flux factor and the product of two shell measures are invariant; the measure of the final states with a conserved total momentum is supported on a set of lower dimension, and its construction needs a coarea formula, which the pinned Mathlib does not have.

**Interface decision.** `orbitalMoment`, `totalMoment` and `centreOfEnergy` are stated for vectors in `d` space dimensions and a finite index type of particles. A collision is the hypothesis that the particles are at one event. `crossSection ν W F S` takes the measure of the final states and the weight as arguments, and `crossSection_covariant` assumes that the transformation preserves both. The ledger row of §12 is *proved modulo interface* with this interface, and it is closed with the construction of the measure as its remainder.

**Proof status.** `flat_lorentzGenerator`, `orbitalMoment_eq_of_stationary`, `totalMoment_freeMotion`, `sum_orbitalMoment_same_event`, `centreOfEnergy_freeMotion`, `fluxFactor_sq`, `measurePreserving_action_prod` and `crossSection_covariant` are proved. [Orbital charges](../ProjectAinos/SpecialRelativity/OrbitalCharges.lean) · [Cross-section](../ProjectAinos/SpecialRelativity/CrossSection.lean)

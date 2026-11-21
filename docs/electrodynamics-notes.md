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

## ED03. Static potentials are elements of the free ring of the positions

**Observation.** The Hamiltonian of a charge needs the potentials as functions on the phase space that do not depend on the momenta. Mechanics states this for a potential `U` of the phase space by the hypothesis `∂U/∂pᵢ = 0`. For the gauge change this is not enough: the canonical transformation `p ↦ p + e ∇χ` must fix every function of the positions, and for an element of the phase space with `∂U/∂pᵢ = 0` this needs a separate argument. For the image of an element of the free ring of the positions it follows from the universal property of the free ring.

**Interface decision.** The potentials `φ`, `a` and the gauge function `χ` are elements of `FreeSmoothRing (Fin d)`, and `PhaseSpace.ofPosition` is the substitution `xᵢ ↦ qᵢ`. Its derivatives and brackets are stated once in the shared algebra, with the substitution `PhaseSpace.momentumShift c χ`, which is a Poisson automorphism. The fields are `electricField φ` and the antisymmetric tensor `magneticTensor a` in every dimension; in three dimensions `Σⱼ Fᵢⱼ vⱼ` is `(v × B)ᵢ`. The static gauge of ED01 is `uniformScalar E = −E x₀`, and `landauPotential B` is a static potential of a uniform magnetic field; these are the instances of `isIntegral_p_of_cyclic`.

**Proof status.** `ChargedParticle.canonical_kineticMomentum_hamiltonian`, `isTrajectory_iff_lorentzForce`, `momentumShift_hamiltonian`, `isTrajectory_gaugeShift` and `isIntegral_p_uniformScalar` are proved. [Functions of the positions](../ProjectAinos/SmoothAlgebra/Poisson/Position.lean) · [Hamiltonian](../ProjectAinos/Electrodynamics/Hamiltonian.lean) · [Examples](../ProjectAinos/Electrodynamics/HamiltonianExamples.lean)

## ED04. The Hamiltonian and the action are compared through the equation of the force, and the flow is complete

**Observation.** The plan compared the action of space-time with the Hamiltonian through a general statement about graphs and a Legendre correspondence. As for the free particle (SR07), the comparison is shorter through the equations. On a graph `t ↦ (t, x(t))` the equation `m dU/dt = e F♯ γ̇` of space-time has four components. Its difference of the two sides is orthogonal to the velocity `(1, ẋ)`, because the force and the acceleration are, so the time component follows from the three space components. These are `d/dt (m γ ẋ) = e (E + ẋ × B)`, and with `p = m γ ẋ + e a(x)` they are Hamilton's equations. A second observation is that the flow of the Hamiltonian is complete for every pair of smooth static potentials. The field of the Hamiltonian has no bound of linear growth, since `∇φ` can grow faster. The speed is less than one, so in a time `T` the position stays in a ball, where the force is bounded.

**Interface decision.** `stationary_graph_iff_lorentzForce` is stated for a `C²` curve of positions with a speed less than one on a closed interval, and `stationary_graph_iff_hamilton` adds `m > 0`. The curve in the phase space is `phaseCurve m e a x`. A trajectory of the Hamiltonian is defined for all times, so `stationary_graph_of_isTrajectory` holds on every interval. The completeness is the shared statement `flowDomain_eq_univ_of_bounded_inl` for a field on `ι ⊕ κ → ℝ` whose first components are bounded and whose second components are bounded where the first co-ordinates are bounded. The comparison is in three dimensions, where the action of space-time is defined.

**Proof status.** `ChargedParticle.stationary_graph_iff_lorentzForce`, `stationary_graph_iff_hamilton`, `stationary_graph_of_isTrajectory`, `flowDomain_hamiltonianField` and `measurePreserving_hamiltonianFlow` are proved. [Static field](../ProjectAinos/Electrodynamics/StaticField.lean) · [Bounded velocities](../ProjectAinos/SmoothGeometry/ODE/FlowBounded.lean)

## ED05. In a constant field the closed forms come from one identity of the generator

**Observation.** In the proper time the four-velocity satisfies `u′ = A u` with the constant linear map `A = (e/m) F♯`, so the motion exists for all proper times for every constant field, and it is unique. The closed forms of the electric and the magnetic field are the same statement: for a field `F = α ∧ β` of two covectors, `A` is a multiple of the infinitesimal Lorentz transformation `α ⊗ β♯ − β ⊗ α♯` of SR17, and `A³ = κ A` with `κ = (e/m)² (⟨α, β⟩² − ⟨α, α⟩ ⟨β, β⟩)`. Then `u = u₀ + s A u₀ + c A² u₀` for functions with `s′ = 1 + κ c` and `c′ = s`: hyperbolic functions for `κ > 0`, trigonometric functions for `κ < 0` and powers for `κ = 0`. A field is of this kind if and only if `E · B = 0`; the case `κ = 0` is a null field. Parallel fields are the sum of two such fields whose generators have zero products, and then the velocities add. The existing example `uniformPotential` has the potential `−E t dx`; the potential here is `½ ι_x F` for every constant field.

**Interface decision.** `ConstantField.potential F` is the linear potential `½ ι_x F`, and `ConstantField.generator m e F` is a continuous linear map. `velocity` and `motion` are `LinearODE.linearVelocity` and `LinearODE.linearMotion`, which are shared and are stated for a bounded operator of a Banach space. `IsSimple F α β` is the hypothesis `F(v, w) = α(v) β(w) − α(w) β(v)`; the electric part and the magnetic part of `Examples.uniformField` and the field `nullField E` are its instances. `motion_eq_hyperbola` compares the motion with the hyperbola of the earlier example, without a gauge transformation: the two potentials have the same field. The curves in the time of an observer, the catenary and the drift, are not derived. The reduction of a field with `E · B ≠ 0` to parallel fields is the normal form of §25.

**Proof status.** `ConstantField.stationary_motion`, `deriv_eq_velocity_of_stationary`, `generator_cube`, `velocity_of_pos`, `velocity_of_neg`, `velocity_of_zero`, `velocity_add` and `motion_eq_hyperbola` are proved. [Constant field](../ProjectAinos/Electrodynamics/ConstantField.lean) · [Examples](../ProjectAinos/Electrodynamics/ConstantFieldExamples.lean) · [Linear motion](../ProjectAinos/SmoothGeometry/ODE/LinearMotion.lean)

## ED06. The components for a moving observer are those of the pullback by the inverse boost

**Observation.** The transformation of `E` and `B` has two readings with opposite signs of the velocity. `boost β` maps the four-velocity of the observer with the velocity `β` to the axis of the time. A vector with the components `x` for the observer at rest has the components `boost β x` for the moving observer, so a two-form has, for the moving observer, the components of its pullback by the inverse boost, which is `boost β.neg`. The pullback by `boost β` itself gives the formulas with `−V`.

**Interface decision.** `electricVector F` and `magneticVector F` are the triples `F(eᵢ, e₀)` and `(F₂₃, F₃₁, F₁₂)` in the frame of the co-ordinates; they are the components of `electric` and `magnetic` for `restObserver 3`. The catalogue is stated for the velocity `V` along the first axis, `axisVelocity V hV`, for both readings: `electricVector_boost`, `magneticVector_boost` for the pullback by the boost and `electricVector_moving`, `magneticVector_moving` for the moving observer. `electric_observer_apply` and `magnetic_observer_apply` say that the second are the components of the electric and the magnetic covector of the observer `β.observer` on the axes `boost β.neg eᵢ`; the magnetic statement uses that the Hodge star commutes with a proper Lorentz transformation. The formula for a velocity in a general direction is not stated.

**Proof status.** `boost_axisVelocity_apply`, `electricVector_boost`, `magneticVector_boost`, `electricVector_moving`, `magneticVector_moving`, `electric_observer_apply` and `magnetic_observer_apply` are proved. [Field transformation](../ProjectAinos/Electrodynamics/FieldTransformation.lean)

## ED07. The kinds of a field are stated for its generator, and no frame is needed

**Observation.** ED05 left the field with `E · B ≠ 0` to a normal form: a frame in which `E` and `B` are parallel. The frame is not needed for the motion. The generator `G = F♯`, the map `v ↦ (E · v, v⁰ E + v × B)`, satisfies `G³ = −I₁ G − I₂ D` and `G D = −I₂` with the dual map `D` of the triples `−B` and `E`, so `G⁴ = −I₁ G² + I₂²`: the equation of Cayley and Hamilton with the invariants `I₁ = B² − E²`, `I₂ = E · B` as coefficients. For `I₂ = 0` the first identity is `G³ = −I₁ G`, which is the hypothesis of the closed forms of ED05 without the hypothesis that the field is a product of two covectors. For `I₂ ≠ 0` the quartic is `(G² − a²)(G² + b²) = 0` with `a, b > 0`, and `(G² + b²)/(a² + b²)` is a projection that commutes with `G`; on its range `G² = a²` and on its kernel `G² = −b²`. The motion is then the sum of a hyperbolic and a circular motion. This is the content of the normal form in a form that does not choose a basis.

**Interface decision.** The identities are proved for the map `forceVector E B` of two real triples, by a calculation in components, and transferred to `ConstantField.generator m e F` with `lorentzForce_vectors`. The four kinds are four theorems with hypotheses on the invariants; `exists_rates` gives the rates `a`, `b` for `I₂ ≠ 0`. The statement for an operator, `LinearODE.linearVelocity_eq_of_quartic`, is shared and rests on `linearVelocity_eq_of_projection`. The ledger row of §25 is *proved* with this scope written: the kinds are properties of the generator, and a frame with parallel fields is not constructed. For `I₂ ≠ 0` the closed form is stated for the four-velocity; the world line is its integral and is not written out.

**Proof status.** `forceVector_cube`, `forceVector_dual`, `ConstantField.generator_quartic`, `velocity_of_scalarInvariant_neg`, `velocity_of_scalarInvariant_pos`, `velocity_of_invariants_zero`, `velocity_of_quartic`, `exists_rates` and `velocity_uniformField_closed` are proved. [Field classification](../ProjectAinos/Electrodynamics/FieldClassification.lean) · [Linear motion](../ProjectAinos/SmoothGeometry/ODE/LinearMotion.lean)

## ED08. On a manifold a potential is a one-form on the whole manifold

**Observation.** The exterior derivative of smooth forms on a manifold, with `d² = 0`, additivity and naturality for smooth maps, is in the shared geometry. With it the statements of §§16 and 18 for a manifold are short: the field of a potential is closed, it is unchanged by `A ↦ A + dχ`, and it is natural. A potential in this sense exists on the whole manifold. A field on a manifold that has potentials only on the sets of a cover, which differ by gauge changes on the overlaps, is a connection of a line bundle; this is the target E8 and needs the bundle.

**Interface decision.** `Curved.fieldOf A` is `smoothExteriorDerivative A` for `A : Curved.Potential`, and a gauge function is a smooth form of degree zero. `fieldOf_ofFlat` compares it with `fieldTensor` for a smooth potential on flat space-time. The ledger rows of §16 and §18 are *proved* with the scope of potentials on an open set of flat space-time or on a whole manifold, and they name E8 as not treated.

**Proof status.** `Curved.fieldOf_closed`, `fieldOf_gaugeShift`, `source_gaugeShift`, `maxwell_gaugeShift_iff`, `fieldOf_pullback` and `fieldOf_ofFlat` are proved. [Potentials on a manifold](../ProjectAinos/Electrodynamics/CurvedPotential.lean)

## ED09. The source enters the Lagrangian as minus the coefficient of `A ∧ J`, and the matter current is `k = −j`

**Observation.** The flat vacuum action of ED02 has the first variation `−∫ dη ∧ ⋆F = −∫ η ∧ d⋆F`. With the term `−coefficient (A ∧ J)` the stationarity is `d⋆F + J = 0`, which is `dH = J` with the excitation `H = −⋆F` of `Curved.Maxwell`; the sign is not a choice once the vacuum action and the excitation are fixed. For a matter current `k` the current form `J = −ι_k vol` makes the source term `+A(k)`, because `a ∧ ι_v vol = a(v) vol`. This is the sign of the coupling `e A(γ̇)` of a charge, so a point charge has the current `k = e δ γ̇` with a positive weight. Since `Curved.currentForm j = ι_j vol`, the vector `j` of the Maxwell system is `−k`, as the plan required.

**Interface decision.** `SourcedAction.lagrangian J` takes any current three-form, and `matterCurrentForm k` is the current form of a vector field. The statements that need the vacuum computation are stated for `C²` currents; the gauge statements need only `C¹`. The change under a gauge change uses Stokes's theorem for the compactly supported form `χ J`, with the Leibniz rule `d(χ J) = dχ ∧ J + χ dJ` from the wedge algebra. A gauge function without compact support, and the current of a point charge, are not treated.

**Proof status.** `SourcedAction.stationary_iff`, `stationary_iff_excitation`, `action_gaugeShift`, `action_gaugeShift_eq_iff`, `coefficient_wedge_interior_volume`, `lagrangian_matterCurrentForm` and `matterCurrentForm_eq_currentForm` are proved. [Sourced action](../ProjectAinos/Electrodynamics/SourcedAction.lean) · [Matter current](../ProjectAinos/Electrodynamics/MatterCurrent.lean)

## ED10. The vector equations come from four components of a three-form

**Observation.** A three-form on space-time has four components, `(1, 2, 3)` and `(0, j, k)` for the three cyclic pairs. For a field `G` with the components `E` and `B` of F5, `dG(e₁, e₂, e₃) = div B` and `dG(e₀, e_j, e_k) = ∂_t Bᵢ + (curl E)ᵢ`. The same lemmas apply to the excitation, whose electric part is `B` and whose magnetic part is `−E`; with `−ι_k vol(e₁, e₂, e₃) = −ρ` and `−ι_k vol(e₀, e_j, e_k) = 𝐤ᵢ` they give `div E = ρ` and `curl B − ∂_t E = 𝐤`. No observer field is needed: the frame is that of the co-ordinates.

**Interface decision.** The fields are functions `electricField G i`, `magneticField G i`, and their derivatives are `partialAt f μ x = Df(x)(e_μ)`. The theorems derive the vector equations from the forms; the converse would need the extensionality of three-forms by their four components and is not stated. The example `t dt ∧ dx` with the current `∂x` is proved through the comparison with `Curved.Examples.magneticExcitation_derivative`, so the flat and the native exterior derivative agree on it.

**Proof status.** `exteriorDerivative_spatial`, `exteriorDerivative_temporal`, `homogeneous_of_closed`, `inhomogeneous_of_excitation`, `maxwell_of_stationary`, `SourcedAction.Examples.stationary_example` and `maxwell_example` are proved. [3+1 equations](../ProjectAinos/Electrodynamics/ThreePlusOne.lean) · [Example](../ProjectAinos/Electrodynamics/SourcedActionExamples.lean)

## ED11. The balance of the charge is stated on a box of the co-ordinates

**Observation.** Mathlib has the divergence theorem on a box `[a, b]` of `ℝⁿ⁺¹` for a field that is differentiable in its interior. For a current with `div k = 0`, the face `x⁰ = const` gives the charge in the spatial box at the two times, and the other six faces the flux. A general region of integration needs a divergence theorem on manifolds with boundary, which the pinned Mathlib does not have. The equation of continuity itself follows from the field equation: `d(−ι_k vol) = −(div k) vol`, and `dJ = d(dH) = 0` where `dH = J` on an open set, for a `C³` potential.

**Interface decision.** `charge k a b t` and `faceFlux k a b i` are the integrals over the faces of the box, and `charge_balance` is the statement with the time faces separated. `divergence4 k = Σ_μ ∂_μ k^μ` is the divergence in the co-ordinates.

**Proof status.** `coefficient_exteriorDerivative_matterCurrentForm`, `exteriorDerivative_matterCurrentForm_eq_zero_iff`, `divergence4_eq_zero_of_stationary` and `charge_balance` are proved. [Charge balance](../ProjectAinos/Electrodynamics/ChargeBalance.lean)

## ED12. The stress tensor is a bilinear form, and its balance is proved in components

**Observation.** The tensor `T_{μν} = F_{μα} F_ν{}^α − ¼ g_{μν} F²` is the bilinear form `T(v, w) = g⁻¹(ι_v F, ι_w F) − ¼ g(v, w) F²`. In this form its value on an observer needs no frame: `ι_u F = −E_u`, `g(u, u) = −1` and `F² = 2(|B_u|² − |E_u|²)` give `T(u, u) = ½(|E_u|² + |B_u|²)`. Its divergence is a statement about derivatives, and in the frame of the co-ordinates its components are the energy density, the vector of Poynting with a sign for the lower index `0`, and the stress of Maxwell. The two balances `∂_t u + div S = −E · 𝐤` and `∂_t Sᵢ + ∂ⱼ σᵢⱼ = −(ρ Eᵢ + (𝐤 × B)ᵢ)` are then polynomial identities in the six components and their twenty-four derivatives, linear in the four vector equations of ED10.

**Interface decision.** `stressForm` takes a two-form and two vectors; `raisedStress F μ ν` is the component `T^{μν}` of a field as a function. The balances are proved with the product rule for `partialAt`; in the proofs the six components are replaced by free functions (`generalize`), because `fun_prop` uses hypotheses about free functions only and stops at a hypothesis about a field. The tensor of a Lorentzian manifold and the variation of the metric are not part of this wave.

**Proof status.** `poynting_local`, `momentum_local`, `energy_balance`, `momentum_balance`, `stressForm_symm`, `stressForm_trace`, `stressForm_observer`, `divergence_raisedStress_zero` and `divergence_raisedStress_succ` are proved. [Energy and momentum](../ProjectAinos/Electrodynamics/EnergyMomentum.lean) · [Stress tensor](../ProjectAinos/Electrodynamics/StressTensor.lean)

## ED13. Charged dust moves by the force of the particle, and the total stress is conserved

**Observation.** For dust with the four-velocity `U`, the stress `μ U^μ U^ν` has the divergence `U^ν ∂_λ (μ U^λ) + μ U^λ ∂_λ U^ν`. If the mass is conserved and each element moves by the force `ρₑ F♯ U`, which is `lorentzForce ρₑ F U` of the charged particle, the divergence is `F^ν{}_λ k^λ` with `k = ρₑ U`. The field has the divergence `−F^ν{}_λ k^λ`, so the sum is zero. The components of `lorentzForce` are `e E · 𝐯` and `e (v⁰ E + 𝐯 × B)` (from `lorentzForce_vectors`), which match the right-hand sides of the balances of the field.

**Interface decision.** `ChargedDust` is a structure of three functions with no constraint; the normalization `g(U, U) = −1` is not needed for the identity and is not assumed. The equations of the dust and of the field are hypotheses at a point. A fluid with a pressure, and the virial of §34, are not treated; the row of §34 names the trace of the field as its proved part.

**Proof status.** `ChargedDust.divergence_matterStress`, `lorentzForce_zero_eq`, `lorentzForce_succ_eq` and `total_stress_conserved` are proved. `total_stress_conserved_uniform` is an instance: neutral dust that moves uniformly in any constant field satisfies all the hypotheses. [Charged dust](../ProjectAinos/Electrodynamics/ChargedDust.lean)

## ED14. The tensor of §33 is characterized by the variation of the metric in co-ordinates

**Observation.** Target E19 asks for `δ_g S = −½ ∫ T^{EM}_{μν} δg^{μν} vol_g` with the potential held fixed. The density `−¼ F_{ab} F^{ab} √|g|` depends on the potential only through `F`, and the metric is varied with `F_{ab}` fixed, so the variation needs a field of coefficients `F_{ab}`, not a potential. The library has no integral of a density on a manifold (GR02); the integral is taken on an open set of the model space, as in §93.

**Interface decision.** `CoordinateMetric.maxwellStress` is the Hilbert tensor of a fixed antisymmetric field `F_{ab}` for a metric given by coefficients, and `Electrodynamics.maxwellStress_minkowski` identifies it in Minkowski space with `stressForm G` for `F_{ab} = G(e_a, e_b)`. The native tensor on a Lorentzian manifold is not constructed. The comparison with the canonical tensor of the translations, which the ledger row of §32 also asks for, is ED15.

**Proof status.** Proved and built. [Hilbert tensor](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinateMatter.lean) · [Comparison with §33](../ProjectAinos/Electrodynamics/HilbertStress.lean)

## ED15. The canonical tensor is compared with the Hilbert tensor in the jet ring, and evaluated on a potential

**Observation.** The canonical tensor of F6 lives in a jet ring, the Hilbert tensor of ED14 in the co-ordinates of a metric. In the jet ring the comparison is an identity: `Θ^μ_ν + T^μ_ν + Σₐ Dₐ(F^{μa} A_ν) = −A_ν E_μ(L)` for the Lagrangian of a one-form with any constant symmetric matrix, and the term `F^{μa} A_ν` is antisymmetric in `μ, a`, so its divergence vanishes because total derivatives commute. The two settings meet in the standard jet ring, whose prolongation substitutes the jet of a smooth potential.

**Interface decision.** `FieldJetRing.symmetricStress η μ ν` is defined in the jet ring with `L = quadraticLagrangian (gaugeConstants η)`, and `Electrodynamics.prolongation_symmetricStress` proves that on the jet of a potential with the Minkowski matrix it is `η^{μα} T_{αν}` with `CoordinateMetric.maxwellStress` for `F = dA`; `gauge_quadratic_identity` is `½ C w w = −¼ F²` for any symmetric matrix. The canonical tensor keeps the sign of F6, `T^0_0 = H`; the mixed Hilbert tensor is minus the energy density in `(−+++)`, so the relation carries a minus sign. Only the free field in Minkowski space is compared; a general Lagrangian and a curved background are not.

**Proof status.** Proved and built; the ledger row of §32 is *proved* in this scope. [Jet ring](../ProjectAinos/Variational/FieldJet/Belinfante.lean) · [Evaluation](../ProjectAinos/Electrodynamics/CanonicalStress.lean)

## ED16. The curved field action is stated in co-ordinates, and its stationarity gives the sourced half of the equations

**Observation.** Target E13 asks for the integral on an oriented curved manifold, the native equation, the component equivalence and the flat functional. The library has no integral of a density on a manifold (GR02), so the functional is taken on an open set `U` of the model space with the density `√|g|`, as in §93. The density is exactly quadratic in the variation, so the derivative at `0` needs no domination argument beyond the integrability of continuous functions with compact support. Stationarity under variations of the potential gives only `dH = J`; the equation `dF = 0` comes from `F = dA` and is a separate hypothesis on the native field. At the Minkowski metric the flat Lagrangian `−½ coefficient(F ∧ ⋆F)` is `−¼ F_{ab} F^{ab}`, because the coefficient of `F ∧ ⋆G` is the induced pairing of two-forms, and the source term `coefficient(A ∧ ι_j vol)` is `A(j)`.

**Interface decision.** `CoordinateMetric.potentialAction g j A η ε` takes the current as coordinates `j : E → Fin 4 → ℝ`, continuous on `U`; the physics theorems relate it to a native `CurrentVector` by the components. The native field `F` is given with the components `∂_a A_b − ∂_b A_a`. The positive coupling `+A_b k^b` of a matter current is the current `−k`, as in the flat `matterCurrentForm`. The charge on a curved background is in general relativity (GR15), with its flat case against `stationary_iff_lorentzForce`.

**Proof status.** Proved and built; the ledger row of §17 is *proved*, and the remark of §27 names the curved functional. [Field action](../ProjectAinos/SmoothGeometry/Lorentzian/CoordinatePotential.lean) · [Maxwell equations](../ProjectAinos/Electrodynamics/CurvedAction.lean)

## ED17. The virial theorem is an identity on a box for a smooth stress with support

**Observation.** The divergence theorem on a box, applied to `P^μ = Σ_α x_α T^{μα}`, gives the change of the virial moment as the integral of the spatial trace once the stress is conserved and vanishes on the spatial faces. Symmetry of the stress is not needed, only conservation in the first index. A time average then needs only a bounded moment. Charged dust cannot be at rest, because `ρₑE = 0` forces `E = 0` on its support, and free dust disperses; so the dust corollary has only the static neutral instance. The improvement stress `(∂^μ∂^ν − η^{μν}□)χ` is identically conserved and can have a nonzero spatial trace, so it shows that the hypotheses are not vacuous.

**Interface decision.** Finite motion is read as support in one spatial box for all times (decision 6 on #135), with the moment bounded. The decay version over all of space is not stated: it needs face fluxes on growing cubes and dominated convergence. Point charges are excluded, since their stress is a distribution.

**Proof status.** Proved and built: the box identity, the Fubini split, the two time averages, the trace-free field stress, the dust corollary with its instance, and the improvement instance. The ledger row of §34 is *proved* in this scope. [Virial](../ProjectAinos/Electrodynamics/Virial.lean) · [VirialExamples](../ProjectAinos/Electrodynamics/VirialExamples.lean)

## ED18. Coulomb orbits are rosettes or fall to the centre, and the fall is a finite exit from the flow domain

**Observation.** In the chart `s = log r` the relativistic Coulomb Hamiltonian is smooth on the whole phase space, so the flow of `hamiltonianField` has a maximal open domain. The orbit functions `X`, `Y` are linear in each other along the angle, which gives the rosette for `ℓ² > α²` with the perihelion spacing `2π|ℓ|/√(ℓ² − α²)`. For attraction with `ℓ² ≤ α²` no all-time solution exists: `p_s/r` strictly decreases, so `p_s` becomes negative and bounded away from zero, and the radius reaches zero in finite time. One argument covers the radial motion `ℓ = 0`, where the orbit equation is empty. Both the circular orbit and the fall need `m > 0`; for `m < 0` the flow is the time-reversed repulsive problem.

**Interface decision.** The rosette is stated for trajectories defined for all times, with the circular orbit as instance. The spiral forms are stated on intervals of a solution, since no all-time trajectory exists. The fall is stated as leaving the flow domain, with the collision `r < ε` before the exit time, using the compactness criterion of the flow domain. The redesign's planned fallback, which assumed no maximal-interval theory, was not needed.

**Proof status.** Proved and built: the Hamiltonian and its brackets, the integrals, the rosette with its perihelia and the circular instance, the spiral forms, the fall to the centre and the collision. The ledger row of §39 is *proved* in this scope; the limit `r → 0` at the exit time and the continuation are not stated. [CoulombMotion](../ProjectAinos/Electrodynamics/CoulombMotion.lean)

## ED19. Larmor's theorem is an identity in the free ring and a bound for given solutions

**Observation.** In the symmetric gauge the kinetic momentum `p − (e/2)B × q` squared splits exactly into `|p|² − e B·(q × p) + (e²/4)|B × q|²`. Dividing by `2m` gives the rotating-frame Hamiltonian at `Ω_L = eB/2m` plus the diamagnetic term. With a common ratio `eₐ/mₐ = γ` the frequency is the same for every particle, which is the content of the theorem. The diamagnetic force is `−(eₐ²/4mₐ)(|B|²qₐ − (B·qₐ)B)`, with Euclidean norm at most `(eₐ²/4mₐ)|B|²|qₐ|`.

**Interface decision.** The identity is stated in the free ring for any momentum-independent `U`, so it holds without regularity. The bound is stated for real functions with an arbitrary force, for given solutions on `[0, L]` that stay in a set where the rotating field is Lipschitz (decision 7 on #135), so a Coulomb potential is admitted away from collisions. Norms are sup norms with the Euclidean bound `Σᵢ qᵢ² ≤ R²`. The ratio is stated as `eₐ/mₐ = γ`.

**Proof status.** Proved and built: the one-particle and `N`-particle identities, the decomposition of the field, the bound in both forms, and the oscillator example. The ledger row of §45 is *proved* in this scope. [Larmor](../ProjectAinos/Electrodynamics/Larmor.lean)

## ED20. Coulomb's law is proved through the point-source pairing

**Observation.** With the derivatives on the density, `Δφ(x) = ∫ K(y) Δρ(x − y) dy`, so `Δφ = −ρ` is the pairing `∫ K Δχ = −χ(0)` for the translated density. The pairing follows from the regularized kernel `1/(4π√(|x|² + ε²))`, whose Laplacian is `−ε⁻³` times a peak of integral 1. Green's identity moves the Laplacian onto it, an approximation of the identity gives `χ(0)`, and dominated convergence removes the regularization. The decay bounds need only a continuous density. Uniqueness follows from the maximum principle on balls, which needs a positive dimension.

**Interface decision.** The potential theory is shared mathematics on `EuclideanSpace ℝ (Fin 3)`, with the convolution in the order `K ⋆ ρ` so that Mathlib differentiates the density. The point source is stated in pairing form; the name `Distribution` is not used. The energy equality uses a cut-off from `ContDiffBump`. Its boundary term is `O(1/R)` by the decay of the potential and its gradient.

**Proof status.** Proved and built: the Laplacian and kernel facts, `Δφ = −ρ`, the decay bounds, the pairing, uniqueness, the static Maxwell equations, the flux of a point charge, the three equal energies and the divergent self-energy. The ledger rows of §§36 and 37 are *proved* in this scope. [Potential](../ProjectAinos/SmoothGeometry/Potential/NewtonPotential.lean) · [Electrostatics](../ProjectAinos/Electrodynamics/Electrostatics.lean) · [ElectrostaticEnergy](../ProjectAinos/Electrodynamics/ElectrostaticEnergy.lean)

## ED21. The moving charge is the boost of a static solution

**Observation.** The current form `−ι_k vol` pulls back under a proper Lorentz map to the form of the transported current `L⁻¹k(L·)`, since `det L = 1`, and the Hodge star commutes with the pullback. The sourced equation is therefore carried to the boosted frame. With `A = −φ dt` the boost gives `A = −γφ′(dt − V dx)` at the comoving position. The field of a moving point charge then follows from the harmonicity of `1/|x|` away from the origin.

**Interface decision.** Static solutions are a structure with an open domain, so the point charge and the smooth Newton potential are both instances; `MovingSource.lean` connects §36 to §38. The world line is the zero set of the present separation `x − Vt e₁`. The converse `excitation_of_inhomogeneous` (3+1 equations ⇒ `d(−⋆F) = J`) is in `SourceCovariance.lean`, and the wave equation uses it.

**Proof status.** Proved and built: the transport theorems, the boosted static solution with `E′` and `B = V × E`, (38.8) off the world line, and the boosted Newton potential. The ledger row of §38 is *proved* in this scope. [SourceCovariance](../ProjectAinos/Electrodynamics/SourceCovariance.lean) · [MovingCharge](../ProjectAinos/Electrodynamics/MovingCharge.lean) · [MovingSource](../ProjectAinos/Electrodynamics/MovingSource.lean)

## ED22. The wave equation is gauge-fixed Maxwell, and its uniqueness comes from the energy identity

**Observation.** `div E = −□φ − ∂ₜL` and `curl B − ∂ₜE = −□a + ∇L`, so the Lorenz condition turns Maxwell's equations into `□A_ν = −k_ν`. For a conserved current the Lorenz divergence itself solves the wave equation; with vanishing initial data and support in a box, the energy current `(½((∂₀u)² + |∇u|²), −∂₀u ∇u)` shows that it stays zero. A plane wave `f(ℓx)a` needs `ℓ` null and `a` transverse, and is then transverse in the frame of any observer. For monochromatic waves the gauge classes of the amplitudes are cosets of `span ℓ`, and the transverse ones modulo `ℓ` have dimension 2.

**Interface decision.** The box and the divergence are in co-ordinates through `partialAt`. The uniqueness theorem asks for a `C²` function on all of space-time, because the divergence theorem on a box needs a `C¹` energy current there. The polarization quotient is taken in `FourCovector ⧸ span ℓ`, as the kernel of `⟨ℓ, ·⟩`, since a quotient of a submodule of a submodule was not found by instance search. Complex amplitudes are real pairs.

**Proof status.** Proved and built: the box identities, the equivalence in Lorenz gauge, the gauge change, the propagation of the gauge and the constraints, uniqueness, the plane wave with its transversality and stress, the gauge classes, the two polarizations, the ellipse and the Doppler formula. The ledger rows of §§46–48 are *proved* in this scope; the existence of a gauge function and finite speed of propagation are not stated. [WaveEquation](../ProjectAinos/Electrodynamics/WaveEquation.lean) · [PlaneWave](../ProjectAinos/Electrodynamics/PlaneWave.lean) · [Monochromatic](../ProjectAinos/Electrodynamics/Monochromatic.lean)

## ED23. The coherency matrix is a limit of averages, stated as a premise with instances

**Observation.** The average of `E₀E₀†` over `[0, T]` is positive semidefinite, because `x†Mx` is the average of `|x†E₀|²`. The cone is closed, so the limit is positive too. For a Hermitian 2×2 matrix, `s₁² + s₂² + s₃² = s₀² − 4 det J`, so positivity is the Stokes bound. A 2×2 Hermitian matrix with nonnegative trace and determinant is positive. The positivity needs a continuous amplitude: an interval integral of a non-integrable function is zero, which can break positivity entrywise.

**Interface decision.** The long-time limit is the named premise `HasCoherenceMatrix`, with constant, incoherent and unpolarized instances. The ensemble is classical; no quantum module is imported.

**Proof status.** Proved and built. The ledger row of §50 is *proved* in this scope. [Coherence](../ProjectAinos/Electrodynamics/Coherence.lean)

## ED24. Multipole remainders are Taylor bounds of the kernel outside a ball

**Observation.** On the segment from `x` to `x − y` with `|y| < |x|`, every point stays at distance `|x| − |y|` from the origin. So Taylor's theorem bounds the multipole remainders by the next derivative of the kernel there. The second and third derivatives have explicit forms, which give the constants `1/(4π)` for the dipole and quadrupole remainders. At a general order, the homogeneity of degree `−(n + 1)` and the compactness of the unit sphere give a constant. The translation law is proved by comparing the expansions of `φ(x + b)` and of the translated density along a ray, with a lemma that a polynomial of degree `k` in `t` bounded by `t^{k+1}` vanishes.

**Interface decision.** The kernel estimates are shared mathematics in `Potential/Multipole.lean`. Densities need only be continuous with support in a ball. The external potential in §42 is bounded through a hypothesis on its next derivative over the source ball, not a supremum. The translation law is stated for `x ≠ 0`, where the derivatives of the kernel are not junk values.

**Proof status.** Proved and built, with the dipole–dipole case for a neutral source in the field of a point dipole. The ledger rows of §§40–42 are *proved* in this scope. [Potential multipoles](../ProjectAinos/SmoothGeometry/Potential/Multipole.lean) · [Multipole](../ProjectAinos/Electrodynamics/Multipole.lean)

## ED25. Magnetostatics reuses the Newton potential componentwise

**Observation.** The vector potential is the Newton potential of each component of the current. Its divergence is the potential of `div j`, so it vanishes for a conserved current. Then `curl curl a = ∇div a − Δa = j`. Uniqueness follows componentwise from the harmonic uniqueness. A conserved current of compact support has a vanishing integral and antisymmetric first moments, so its first nonvanishing far field is the magnetic dipole.

**Interface decision.** `curl3` and `div3` act on fields of space, and the space-time equations are obtained through `potentialOf 0` and `Minkowski.space`. The matter model of §44 is a stationary flow with one ratio `e/m`, with the instance of a rigidly rotating radial density. L&L's time averages over point particles are not used. Biot–Savart is stated outside the support only, where the integral is not singular.

**Proof status.** Proved and built. The ledger rows of §§43 and 44 are *proved* in this scope. [Magnetostatics](../ProjectAinos/Electrodynamics/Magnetostatics.lean) · [MagneticMoment](../ProjectAinos/Electrodynamics/MagneticMoment.lean)

## ED26. The Fourier solution of the wave equation is a Fourier integral on the light cone

**Observation.** Writing the solution as the Fourier integral of a density against the image of Lebesgue measure on the two sheets `s = ±|ξ|` of the light cone makes Mathlib's theorems on Fourier integrals of finite measures apply. They give smoothness in `(t, x)` and the derivatives directly. The wave equation holds because the second-derivative integrand is a multiple of `−s² + |η|²`, which vanishes on the cone. The temporal Plancherel identity comes from Mathlib's Schwartz Plancherel, and (49.8) from the conjugate symmetry of the transform of a real signal.

**Interface decision.** Mathlib's normalization `e^{−2πiνt}` is used, with L&L's `f_ω = 𝓕f(−ω/2π)`. The propagator `sin(2π|ξ|t)/(2π|ξ|)` is `t·sinc(2π|ξ|t)`, smooth through `ξ = 0`. The solution is not shown to be a Schwartz function in space.

**Proof status.** Proved and built. The ledger row of §49 is *proved* in this scope. [WaveSolution](../ProjectAinos/SmoothGeometry/Fourier/WaveSolution.lean) · [Spectral](../ProjectAinos/Electrodynamics/Spectral.lean)

## ED27. The Coulomb kernel is a Fourier multiplier in pairing form, by Gaussian subordination

**Observation.** `1/|z| = π^{−1/2}∫₀^∞ t^{−1/2}e^{−t|z|²} dt`. The Gaussian has an explicit transform, and Fubini with the local integrability of `|ξ|⁻²` in three dimensions gives `∫K𝓕χ = ∫χ/(4π²|ξ|²)` for every Schwartz `χ`. The symbol has no temperate growth, so the result is stated as a pairing and, for the potential, in `𝓢′` through the bounded potential; it is not a multiplier operator. The route of decision 8 closed, so its fallback was not needed.

**Interface decision.** The zero-frequency prescription is identified against constants only: `φ + c` has the extra term `c δ₀`, and only `c = 0` decays. The classification of all tempered solutions, which differ by harmonic polynomials, needs the structure of distributions supported at a point and is not claimed.

**Proof status.** Proved and built. The ledger row of §51 is *proved* in this scope. [KernelFourier](../ProjectAinos/SmoothGeometry/Potential/KernelFourier.lean) · [CoulombFourier](../ProjectAinos/Electrodynamics/CoulombFourier.lean)

## ED28. The cavity is the periodic box, with explicit conductor modes

**Observation.** A periodic box rescales to the unit torus, where Mathlib has Fourier coefficients and Parseval for the Haar probability measure. The derivative of a coefficient comes from the translation law, without boundary terms. The wave equation gives `ä_k = −ω_k²a_k`, and the Coulomb gauge gives transversality. Lagrange's identity turns `|K × a_k|²` into `ω_k²|a_k|²`, so the energy is a sum over the modes. The conductor modes are periodic with periods `2Lᵢ`, so the energy theorem applies to them on the doubled box.

**Interface decision.** The cavity is the periodic box of L&L (decision 9 on #135), with the torus measure fixed by a local instance. The conductor modes are explicit. Their completeness by reflection to the doubled box is within reach (about 300 lines with a bounded-measurable Parseval) and is not stated here; it is not a genuine remainder reason.

**Proof status.** Proved and built. The ledger row of §52 is *proved* in this scope. [CavityModes](../ProjectAinos/Electrodynamics/CavityModes.lean)

## ED29. The retarded potentials need no Green-operator hypothesis

**Observation.** The outline made §62 conditional on a causal Green operator (E25). In flat space-time the retarded integral is explicit, and the identity `∫ (□f)(t − |y|, x − y)/(4π|y|) dy = f(t, x)` is proved directly. Away from `y = 0`, `□f(t − r, x − y)/r` is the divergence of `V_i = ∂ᵢf/r − ∂ₜf yᵢ/r² − f yᵢ/r³` evaluated at the retarded point. Against a smooth cut-off about the origin the integral becomes a peak-function average of `f + r∂ₜf − y·∇f`, whose value at the origin is `f(t, x)`. No divergence theorem on balls is needed. This corrects the outline's judgement that §62 is conditional.

**Interface decision.** The retarded integral is shared mathematics on `ℝ × ℝ³` with the Euclidean norm, with a continuous linear equivalence to the electrodynamics space-time. Sources are required to have support moving slower than light (`SubluminalSupport`), of which compact support is an instance. Uniqueness is among solutions that vanish in the past with bounded spatial support. For §64 the transform is taken in time at fixed position, in Mathlib's normalization.

**Proof status.** Proved and built. The ledger rows of §§62 and 64 are *proved* in this scope. [RetardedIntegral](../ProjectAinos/SmoothGeometry/Wave/RetardedIntegral.lean) · [RetardedPotential](../ProjectAinos/Electrodynamics/RetardedPotential.lean) · [RetardedSpectrum](../ProjectAinos/Electrodynamics/RetardedSpectrum.lean)

## ED30. The retarded time is smooth off the world line, and its gradient is null

**Observation.** For a world line slower than light, `s ↦ t − s − |x − r(s)|` decreases with slope at most `−1 + v₀`, so the retarded time exists and is unique, and it is smooth off the world line by Mathlib's implicit function theorem; the global retarded time agrees with the implicit function because the solution is unique. Its gradient is null, `⟨∂τ, ∂τ⟩ = 0`, so the third derivative of the world line, which multiplies `⟨∂τ, ∂τ⟩`, never appears in `□φ` and `□𝐚`. With `□τ = −2/(R − R·v)` both vanish off the world line, and the Lorenz condition gives the vacuum equations there. The fields (63.8)–(63.9) follow, and the uniform motion is exactly the boosted Coulomb field of §38.

**Interface decision.** `SubluminalWorldline` is a smooth path with `|ṙ| ≤ v₀ < 1` for all times, with the uniform, rest and circular instances. The retarded quantities are functions of `(t, x)` in the namespace of the world line. The fields are split into the velocity field (`∝ 1/R²`) and the acceleration field (`∝ 1/R`), with light-cone forms at the event `(τ + ρ, r(τ) + ρn)` for §73.

**Proof status.** Proved and built. [RetardedTime](../ProjectAinos/Electrodynamics/RetardedTime.lean) · [LienardWiechert](../ProjectAinos/Electrodynamics/LienardWiechert.lean)

## ED31. The point charge is the source of its field by a light-cone change of variables

**Observation.** In the co-ordinates `(τ, y) ↦ (τ + |y|, r(τ) + y)` the Jacobian is `1 − ŷ·ṙ(τ)`, which cancels the denominator of the Liénard–Wiechert potentials: `φ dt d³x = e dτ d³y/(4π|y|)`. The map is a bijection from `ℝ × (ℝ³ ∖ 0)` onto the complement of the world line, a null set, by the uniqueness of the retarded time. The advanced identity `∫ □u(τ + |y|, x + y)/(4π|y|) dy = u(τ, x)` follows from the retarded one by `(t, x) ↦ (−t, −x)`. Pairing the potential with `box χ` gives `∫ φ box χ = −e ∫ χ(t, r(t)) dt`, so `box A_μ = −k_μ` for the current of the point charge, as for smooth currents. This replaces the δ-function step `∫ δ(t′ − t + R(t′)) dt′ = 1/(1 − n·v)` of Landau–Lifshitz by a change of variables.

**Interface decision.** The identity is stated against `C²` test functions of compact support on space-time, with no distribution type. The work is done on `ℝ × ℝ³` and transported by the measure-preserving splitting of space-time. The potentials are locally integrable.

**Proof status.** Proved and built, for every world line slower than light. [LienardWiechertSource](../ProjectAinos/Electrodynamics/LienardWiechertSource.lean)

## ED32. The flux at infinity needs charge conservation for the transversality of `E`

**Observation.** For a source localized in a fixed ball for all times, `R` times the retarded integral at `(u + R, Rn)` tends to the amplitude `(4π)⁻¹ ∫ f(u + ⟨n, y⟩, y) dy`, uniformly on the sphere, with a rate `C/R`. A spatial derivative of the amplitude is `−n` times its time derivative. The magnetic limit is `R B → ∂ᵤÃ × n` without further hypotheses. The electric limit is `R E → n⟨n, ∂ᵤÃ⟩ − ∂ᵤÃ` only because charge conservation gives `∂ᵤφ̃ = ⟨n, ∂ᵤÃ⟩`; otherwise a longitudinal term remains. The radial Poynting flux is then `|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩²`, and the flux through large spheres at fixed retarded time tends to the radiated power by dominated convergence.

**Interface decision.** `LocalizedSupport a f` (support in `|y| ≤ a` for all times) is shared mathematics and is equivalent to `SubluminalSupport a 0 f`. The amplitude, the flux through a sphere and the radiated power are defined once in `Radiation/Basic.lean` and used by the far zone, the near zone and the multipole expansions.

**Proof status.** Proved and built for `C²` conserved currents. [FarField](../ProjectAinos/SmoothGeometry/Wave/FarField.lean) · [Radiation/Basic](../ProjectAinos/Electrodynamics/Radiation/Basic.lean) · [FarZone](../ProjectAinos/Electrodynamics/Radiation/FarZone.lean)

## ED33. The near-zone split of the dipole flux is exact at every radius

**Observation.** The outline asked for a controlled expansion separating the near-zone energy from the outgoing flux. For a point dipole with a smooth moment the split is exact at every radius `R > 0`: the flux through the sphere is `|d̈(t − R)|²/(6π) + dQ_R/dt` with `Q_R = (|d + Rḋ|² + R²|ḋ|²)/(12πR³) ≥ 0` at the retarded time. The radial part of `E` does not contribute to the radial flux. Over a pulse the near-zone term integrates out, so the radiated energy does not depend on `R`. This corrects the outline's expectation of an approximate statement.

**Interface decision.** The point-dipole potential is a global potential with Lean's `x/0 = 0`; the field equations are stated pointwise off the origin, and the fields at points `(t, r n)` with `r > 0`, `|n| = 1`, the parametrization of the flux.

**Proof status.** Proved and built. [NearZone](../ProjectAinos/Electrodynamics/Radiation/NearZone.lean)

## ED34. The multipole powers are Taylor expansions of the amplitude in the delay

**Observation.** For the slow family `k_κ(t, x) = (ρ(κt, x), κ𝐣(κt, x))` the amplitude of the far field is exactly `(κ²/4π) ∫ ∂ₛ𝐣(κu + κ⟨n, y⟩, y) dy`, so the expansion of the radiated power needs only Taylor's formula in the delay `κ⟨n, y⟩`, not an expansion of the retarded integral. The `κ⁵` term is odd in `n` and vanishes after the angular integration, which is why the dipole formula `κ⁴|d̈|²/(6π)` has an `O(κ⁶)` remainder while the angular density has only `O(κ⁵)`. The moment tensor `M_{ki} = ∫ y_k ∂ₛ²j_i` splits into the symmetric part `Q'''/2` and the antisymmetric part `ε m̈`, and the angular integral gives `(1/4π)[(1/180) Σ D'''² + (2/3)|m̈|²]`, with no cross term between the two. Charge conservation enters only through the identities `∫ 𝐣 = ḋ` and `∫ (yᵢjₖ + yₖjᵢ) = d/ds ∫ ρ yᵢyₖ`.

**Interface decision.** `LocalizedSource k a M N` bounds the spatial current and its first `N` time derivatives; the density is controlled by conservation. The quadrupole formula assumes `d̈ = 0` at the retarded time, as in Landau–Lifshitz; without it `power_general` gives the `κ⁶` coefficient with the explicit cross term between the dipole amplitude and its second-order correction. The oscillating current `(cos s ∂₁χ, sin s χ e₁)` and its derivative in `x₁` are the dipole and quadrupole instances.

**Proof status.** Proved and built, with explicit constants. [Dipole](../ProjectAinos/Electrodynamics/Radiation/Dipole.lean) · [Multipole](../ProjectAinos/Electrodynamics/Radiation/Multipole.lean)

## ED35. The radiation of a fast charge is taken along the light cone of its retarded position

**Observation.** At the event `(τ + ρ, r(τ) + ρn)` the retarded time is `τ`, so the Liénard–Wiechert field is explicit and the radial Poynting flux times `ρ²` is a polynomial in `1/ρ`; its limit is the angular distribution per unit time of the observer, and the factor `1 − n·v` of (73.9) is the exact derivative `∂τ/∂t`. Liénard's integral reduces, by Archimedes and the moments orthogonal to `v`, to `∫ (1 − s²)/(1 − βs)⁵ ds` and `∫ 1/(1 − βs)³ ds`, which have explicit antiderivatives. The same reduction gives `∫ (n·v) dI = |v|² ∫ dI` for every acceleration: the mean of `1 − cos θ` over the radiated power is exactly `1 − β`, and Markov's inequality bounds the fraction outside the cone of half-angle `c/γ` by `π²/(2c²)`, uniformly in the speed and the direction of the acceleration.

**Interface decision.** The far zone of §73 is the light cone of the retarded position, not a fixed sphere about the origin as in §66. The synchrotron orbit is the prescribed circular world line; its relation to a uniform magnetic field is the three-vector equation `d(mγv)/dt = e v × B` with `mγΩ = −eB`. `Relativistic.cross` is the cross product on `EuclideanSpace ℝ (Fin 3)`, whose norm is the Euclidean one.

**Proof status.** §73 is proved in this scope. §§74 and 77 are closed with stated remainders: the Bessel and Macdonald closed forms of the spectra, and the spectral asymptotics with Airy-type stationary phase, are absent from Mathlib. The harmonic decomposition of §74 with Fourier coefficients and Parseval is within reach and is not stated. [Relativistic](../ProjectAinos/Electrodynamics/Radiation/Relativistic.lean) · [Synchrotron](../ProjectAinos/Electrodynamics/Radiation/Synchrotron.lean) · [Ultrarelativistic](../ProjectAinos/Electrodynamics/Radiation/Ultrarelativistic.lean)

## ED36. The Darwin Lagrangian is reached for point charges through retarded co-ordinates

**Observation.** For smooth slow sources the retarded integral expands in the slowness `κ` with an explicit remainder, the Darwin gauge turns the potentials into (65.6), and the force on a rigid charge is the Euler–Lagrange expression of the Darwin interaction to order `κ²`. No separation is needed there: the second derivatives of `|x − z|` act with no point term. The `O(κ²)` error of the vector potential contains a spatially constant term, which has no curl and whose time derivative is `O(κ³)`, so the force error is `O(κ³)`. Smearing a point charge does not give the point limit of the force, because the constants grow as the smearing radius shrinks. For point charges the Liénard–Wiechert field is therefore expanded directly, in the retarded distance, direction, velocity and acceleration with Taylor remainders to the present time, which avoids solving for the retarded time: it agrees with the field of the point Darwin potentials to `O(κ³)` in `E` and `O(κ²)` in `B` at separated points. The Euler–Lagrange expression of (65.7) for one charge, the others prescribed, is exactly its kinetic term plus the Lorentz force of the point Darwin potentials of the others, which gives the force to order `κ²`.

**Interface decision.** The motions are prescribed (decision 9 on #135): slow paths `R(κt)` with bounded derivatives up to order three and separations in `[δ, ρ]`, with constants uniform in `κ ≤ 1`. The library's Euler–Lagrange residual is `∂L/∂q − d/dt ∂L/∂v`, so it equals plus the force. The smeared interaction tends to the pair term of (65.7) as the charges shrink to points.

**Proof status.** Proved and built; the ledger row of §65 is *proved* in this scope. [SlowSource](../ProjectAinos/SmoothGeometry/Wave/SlowSource.lean) · [DarwinLagrangian](../ProjectAinos/Electrodynamics/DarwinLagrangian.lean) · [DarwinPointCharge](../ProjectAinos/Electrodynamics/DarwinPointCharge.lean)

## ED37. The angular eikonal needs an invertible momentum map, not an invertible mixed Hessian

**Observation.** In three dimensions the point eikonal of a homogeneous medium is constant along the ray and the momentum `n n̂` has length `n`, so the formulation of §55 degenerates; it is stated in transverse planes with transverse momenta. The angular eikonal `f(p, p′) = ψ(r, r′) − p′·r′ + p·r` is a Legendre transform in both points, so it needs the derivative of the momentum map `(r, r′) ↦ (−∂ψ/∂r, ∂ψ/∂r′)` to be invertible. An invertible mixed Hessian is not enough: for free propagation the mixed Hessian is invertible but the momenta do not change under a common translation of both points, so free propagation has no angular eikonal. This corrects the outline, which stated the angular eikonal under the mixed-Hessian hypothesis. The mixed-Hessian condition is the right one for the ray map `(r, p) ↦ (r′, p′)`, which is canonical by the symmetry of the Hessian.

**Interface decision.** Two hypotheses: an invertible derivative of the momentum map for the angular eikonal, an invertible mixed Hessian for the ray map. The paraxial eikonal `(a, b, c)` has the unimodular ray-transfer matrix `[[a/b, 1/b], [(ac − b²)/b, c/b]]`, so a point eikonal exists only for `b ≠ 0`; the thin lens followed by a gap is the instance of the angular eikonal, and free propagation, paraxial and exact, of the canonical ray map. In the free C∞-ring the ray map of a free generating function `−ψ` is a Poisson morphism.

**Proof status.** Proved and built; the ledger row of §55 is *proved* in this scope. [AngularEikonal](../ProjectAinos/Electrodynamics/Optics/AngularEikonal.lean)

## ED38. The curvature of a wave front obeys a Riccati equation that excludes focal points

**Observation.** Along a ray of a `C³` static eikonal `|∇ψ| = 1`, the Hessian satisfies `H′ = −H²`, so `H(l) = H₀(1 + lH₀)⁻¹` and the principal radii become `R + l`. A solution on a closed interval forces `1 + sH₀` to be invertible with inverse `1 − sH(s)`, and `det(1 + sH₀) > 0`: a smooth eikonal never contains a segment that reaches a focal point. The transport equation `2∇a·∇ψ + aΔψ = 0` gives `a = a₀ det(1 + lH₀)^{−1/2}` along the ray, with `Δψ = tr H` by Jacobi's formula, so the amplitude tends to infinity at a focal point and the approximation of geometrical optics is lost there (§58). For a general smooth index the linearized ray map solves the variational equation, and a narrow beam deviates from it by `O(δ²)`.

**Interface decision.** The Riccati equation is shared mathematics for continuous linear maps of a Banach space, with the determinant and trace results in finite dimension. The Hessian is `fderiv ℝ (∇ψ)` and the transport uses Mathlib's Laplacian. One front family `−‖P(x − c)‖` with an orthogonal projection `P` gives the spherical and the cylindrical instances. The phase space of the ray field carries the product norm.

**Proof status.** Proved and built; the ledger row of §56 is *proved*. [Riccati](../ProjectAinos/SmoothGeometry/ODE/Riccati.lean) · [NarrowBundle](../ProjectAinos/Electrodynamics/Optics/NarrowBundle.lean)

## ED39. Image formation is the first variation of the optical length with moving ends

**Observation.** The optical Lagrangian `n(q)|v|` is smooth only for `v ≠ 0`, and its energy `p·v − L` vanishes identically, so the first variation of the optical length along a family of rays is the boundary term `n⟨t̂, δr⟩` at the two ends. With fixed ends all the rays from a point to its image have the same optical length. For a stigmatic bundle the boundary terms agree over the rays, which specialized to the axial ray is the sine condition `n y sin θ = n′ y′ sin θ′`. For an absolute instrument, with a tangent ray in every direction `±v`, the optical length of every object curve equals that of its image, so `n′|Dφ v| = n|v|`; Carathéodory's argument — `⟨D²φ(w, u), Dφ v⟩` is symmetric in `(w, u)` and antisymmetric in `(u, v)`, hence zero — makes `φ` a similarity with ratio `n/n′`.

**Interface decision.** Rays are paths with `γ′ ≠ 0` solving the Euler–Lagrange equation of the optical Lagrangian; families of rays and absolute instruments are given as data, with stigmatism as a hypothesis. The similarity theorem is shared mathematics on any finite-dimensional inner product space. The plane mirror is an instance of the similarity theorem but, with broken rays and a virtual image, not of the smooth single-medium model; the instances of the ray families are reparametrized segments. An instrument whose aperture admits only a cone of directions is not covered.

**Proof status.** Proved and built; the ledger row of §57 is *proved* in this scope. [Imaging](../ProjectAinos/Electrodynamics/Optics/Imaging.lean) · [Similarity](../ProjectAinos/SmoothGeometry/Euclidean/Similarity.lean)

## ED40. The eikonal and transport equations are the two leading orders of an exact expansion

**Observation.** For `a cos(ψ/ε) + b sin(ψ/ε)` the wave operator is exactly `ε⁻²R₂ + ε⁻¹R₁ + R₀`, with coefficients that are (cos, sin) pairs independent of `ε`: `R₂` is `⟨dψ, dψ⟩` times the amplitude, `R₁` is the transport term `2⟨da, dψ⟩ + a□ψ`, and `R₀ = □a cos + □b sin`. So the vacuum equations hold at the two leading orders iff the null eikonal and the transport equations hold, and the `ε⁻¹` term of the Lorenz divergence is the transversality of the amplitudes. The rays, integral curves of the raised gradient, are straight null lines because `d/ds (dψ)^♯ = ½∇⟨dψ, dψ⟩`. Transport alone, without the eikonal equation, conserves the intensity current `½(a² + b²)∂^μψ`; in the static form the intensity times the Jacobian of a ray tube is constant. In a medium the rays of `(|p|² − n²)/2` follow from a complete integral, and `2√((n²/2)(|v|²/2)) = n|v|` identifies Maupertuis' Jacobi length with the optical length, which gives Fermat's principle with no reparametrization.

**Interface decision.** The expansion is shared mathematics on `ℝ × ℝ³` (`□ = ∂ₜ² − Δ`, pairing `(+−−−)`); the potential and `box = −□` use `(−+++)`. An "order by order for all `ε`" statement needs `ψ ≠ 0` at the point, where the phases can be separated. The static intensity statement is for a field smooth on all of `ℝ³`, so the radial instance uses `x` rather than `x/|x|`.

**Proof status.** Proved and built; the ledger rows of §§53 and 54 are *proved* in this scope. [HighFrequency](../ProjectAinos/SmoothGeometry/Wave/HighFrequency.lean) · [Eikonal](../ProjectAinos/Electrodynamics/Optics/Eikonal.lean) · [RayOptics](../ProjectAinos/Electrodynamics/Optics/RayOptics.lean)

## ED41. The error of geometrical optics is an energy estimate, and its relative size is measured on a pair of phases

**Observation.** For a `C²` function with bounded spatial support on `[0, T]`, `E′(t) = ∫ ∂ₜw □w` by integration by parts, so `√(2E(t)) ≤ √(2E(0)) + ∫₀ᵗ ‖□w‖`. If the amplitudes solve the eikonal and transport equations, `□w = □a cos + □b sin` is bounded independently of `ε`, so the energy of the difference between an exact solution and the approximation with the same data is bounded independently of `ε`. The energy of a single real wave oscillates, `½ε⁻² ∫ (b cos − a sin)²|∂ψ|²`, and a lower bound needs non-stationary phase. For the pair of waves with phases `ψ` and `ψ + επ/2`, the real and imaginary parts of `(a − ib)e^{iψ/ε}`, the oscillating terms cancel exactly, the energy is `ε⁻²` times the leading intensity, and the relative error is `O(ε)`. For a localized plane wave `□a = −Δ⊥f`: the error is diffraction, with relative size about `λt/d²`, the Fresnel condition. At a focal point the transported amplitude diverges (ED38), so the estimate is lost there.

**Interface decision.** Supports are bounded on the finite interval `[0, T]` (`BallSupportOn`), since transported amplitudes are not localized for all times; the eikonal and transport equations are required only on the supports. The exact solution is given; an outgoing spherical shell `g(t − r)/r`, with a smooth radius near the origin, is exact for the ansatz and gives the instance.

**Proof status.** Proved and built; the ledger row of §58 is *proved* in this scope. The lower bound for a single real wave is not stated. [Energy](../ProjectAinos/SmoothGeometry/Wave/Energy.lean) · [Error](../ProjectAinos/Electrodynamics/Optics/Error.lean)

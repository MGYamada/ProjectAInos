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

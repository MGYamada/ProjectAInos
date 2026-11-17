# Scalar smeared fields on Minkowski spacetime

The [scalar field module](../ProjectAinos/QuantumFieldTheory/SmearedField.lean)
is an initial part of the [Wightman program](https://github.com/MGYamada/ProjectAinos/issues/46).
It uses Mathlib's complex Schwartz topology and the complex-linear continuous
dual on time-first four-dimensional Minkowski spacetime. The complex Hilbert
inner product is conjugate-linear in its first argument.

A `ScalarField` acts on one dense invariant complex subspace through linear
endomorphisms. For each domain vector the test-to-vector map is continuous
in the Hilbert norm. Hermiticity pairs the test with its pointwise complex
conjugate. The resulting densely defined operator is closable on a complete
Hilbert space because it lies in the closed adjoint of the conjugate-test
operator. Scalar locality is expressed on the common domain using spacelike
separation of closed test supports.

For a fixed domain vector, the vacuum word API proves the adjoint identity
with reverse conjugated order, continuity and complex linearity in each
individual insertion, and positivity of finite sums via the Hilbert norm.
Point evaluation times the identity on the one-dimensional Hilbert space
checks the operator and locality interfaces. Its operators commute for every
pair of tests, so it does not test the causal condition. The models of the
next section do.

## Causal support witnesses and a noncommuting local field

[LocalityExamples](../ProjectAinos/QuantumFieldTheory/LocalityExamples.lean)
addresses [issue #72](https://github.com/MGYamada/ProjectAinos/issues/72).
In the time-first coordinates `intervalQuadratic_spacetime` is
`v₀² − v₁² − v₂² − v₃²`, negative on spacelike vectors. Spacelike vectors
form an open set that is closed under negation and does not contain zero.

`SpacelikeSeparated` is symmetric and unchanged by `conjugate` in either
argument. Tests whose closed supports share a point are not separated, and
only the zero test is separated from itself.

`bump p r hr` is a Schwartz test equal to one at `p` whose closed support is
the closed ball of radius `r` about `p` in the supremum norm of the
coordinates (`tsupport_bump`). Two bump tests are separated exactly when every
pair of points of the two balls has a spacelike difference
(`spacelikeSeparated_bump_iff`). Centres with a spacelike difference have
separated bumps of some small radius (`exists_spacelikeSeparated_bump`), and
centres whose difference is not spacelike never do.

Two witnesses fix the sign. The unit bumps at the origin and at `spacePoint 5`
are spacelike separated (`bump_spacePoint_spacelikeSeparated`). For the unit
bumps at the origin and at `timePoint 10` every pair of support points has a
timelike difference (`bump_timePoint_timelike`), so they are not separated.

`twoPointField p q A B hA hB` is the field `φ(f) = f(p) A + f(q) B` for
symmetric linear maps `A` and `B` defined on the whole Hilbert space, which is
its common domain. Completeness is not assumed. The commutator is

```text
φ(f) φ(g) ψ − φ(g) φ(f) ψ = (f(p) g(q) − f(q) g(p)) (A B − B A) ψ
```

(`twoPointField_commutator`). If `p − q` is not spacelike the field is local
(`twoPointField_isLocal`): for separated tests a nonzero term of the
coefficient would put one insertion point in each support. This proof uses
the separation hypothesis. If `A` and `B` do not commute and `p − q` is
spacelike, small bumps at `p` and `q` violate locality. Hence

```text
(twoPointField p q A B hA hB).IsLocal ↔ ¬ Spacelike (p − q)
```

for noncommuting `A` and `B` (`twoPointField_isLocal_iff`). Reversing the
causal inequality, or weakening the separation of supports, makes this
equivalence and the two witnesses fail.

The proved instance is `pauliField p q`, with `A = σ_x` and `B = σ_z` taken
from the [qubit prototype](quantum-mechanics-prototype.md) as operators on
`EuclideanSpace ℂ (Fin 2)`. Here `[σ_x, σ_z] e₀ = 2 e₁`
(`pauliOperator_commutator`). The field `pauliField 0 (timePoint 10)` is local,
and its insertions at the two unit bumps have commutator `2 e₁` on `e₀`
(`pauliField_timePoint_commutator`); these tests are timelike separated. The
field `pauliField 0 (spacePoint 5)` has the same commutator on the two
spacelike separated unit bumps and is not local
(`pauliField_spacePoint_not_isLocal`).

The typed regressions are in
[QuantumFieldTheoryAPI](../checks/QuantumFieldTheoryAPI.lean).

### Assumptions exercised

These models exercise the common invariant domain, Hermiticity with the
conjugate test, continuity of the orbit maps, and locality with actual
support witnesses. Closability follows from the general theorem.

They do not exercise a vacuum vector, its normalization or cyclicity; an
action of the Poincaré covering group, since the insertion points are not
translation invariant; the spectrum condition; multipoint distributions; a
proper dense domain or unbounded operators; or a free field. The two-point
Pauli field is a regression model for the locality predicate. It is not a
Wightman field.

Joint distributions on multipoint configuration spaces, a normalized cyclic
vacuum and its covering-group action, the joint forward spectrum, and a free
scalar construction remain open in Gate A. Reconstruction and interacting
continuum limits remain subsequent gates.

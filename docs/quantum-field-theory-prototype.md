# Scalar smeared fields on Minkowski spacetime

The [scalar field module](../ProjectAInos/QuantumFieldTheory/SmearedField.lean)
is an initial part of the [Wightman program](https://github.com/MGYamada/ProjectAInos/issues/46).
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
checks the operator and locality interfaces.

Joint distributions on multipoint configuration spaces, a normalized cyclic
vacuum and its covering-group action, the joint forward spectrum, and a free
scalar construction remain open in Gate A. Reconstruction and interacting
continuum limits remain subsequent gates.

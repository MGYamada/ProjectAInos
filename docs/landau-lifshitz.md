# Landau–Lifshitz Correspondence

This cross-reference connects the Project AInos research plan to the English editions of the *Course of Theoretical Physics*. Mechanics has section-level proof targets. Electrodynamics has a preliminary chapter and volume map, and later topics are listed by reference volume. The implementation order follows the [research plan](../README.md).

## Mechanics

Section numbers refer to Volume 1, *Mechanics*, third edition. The targets use the project's smooth algebra over C∞-rings, with analytic hypotheses tracked separately. [Volume 1 contents](https://www.sciencedirect.com/book/9780750628969/mechanics)

The tiers describe proof prerequisites. **A** uses abstract algebra, **A\*** uses explicit algebraic identities, **B** needs analytic interface lemmas, and **C** needs geometric infrastructure. **D** marks a deeper theorem to state with explicit hypotheses. **P** marks a physical or asymptotic argument that needs a precise theorem statement. When two tiers appear, the first applies to the main target.

| Chapter | § | Planned Lean target | Tier |
| --- | ---: | --- | --- |
| I · Equations of motion | 1 | Configuration spaces, tangent states, and coordinate changes | A |
| I | 2 | First variation, Euler–Lagrange equations, and null Lagrangians | A, B |
| I | 3 | Galilei symmetry on jets and Lagrangian quasi-invariance | A, P |
| I | 4 | The quadratic free-particle Lagrangian from boost quasi-invariance and isotropy | B |
| I | 5 | Natural Lagrangians for particle systems and Newton's equations | A\* |
| II · Conservation | 6 | Energy conservation from time-translation symmetry | A |
| II | 7 | Linear momentum from spatial translations | A |
| II | 8 | The Galilean boost integral and centre-of-mass motion | A |
| II | 9 | Angular momentum from rotations and the momentum map | A |
| II | 10 | Scaling for homogeneous potentials and the time-averaged virial theorem | A\*, B |
| III · Integration | 11 | One-dimensional quadrature and the relation between period and action area | B |
| III | 12 | Abel inversion for the turning-point separation and conditions for recovering the potential | B |
| III | 13 | Canonical centre-of-mass and relative coordinates with reduced mass | A\* |
| III | 14 | Central-force reduction and the orbit integral | A\*, B |
| III | 15 | Kepler conics, the Runge–Lenz vector, and the period law | A\*, B |
| IV · Collisions | 16 | Decay kinematics on joint energy and momentum level sets | A\* |
| IV | 17 | Post-collision velocities from elastic conservation laws | A\* |
| IV | 18 | Deflection as a function of impact parameter and cross-section as a pushforward measure | B, C |
| IV | 19 | Rutherford deflection and differential cross-section | A\*, B |
| IV | 20 | Large-impact-parameter asymptotics for small deflections | P |
| V · Oscillations | 21 | Linearization about a nondegenerate minimum and the quadratic flow | B |
| V | 22 | Duhamel's formula for the driven oscillator and energy transfer | B |
| V | 23 | Normal modes by diagonalizing the mass and stiffness forms | A |
| V | 24 | Molecular vibration modes and their decomposition under symmetry | A |
| V | 25 | Damped linear motion and the energy balance | B, A |
| V | 26 | Linear response and resonance with damping | B |
| V | 27 | Monodromy in SL(2, ℝ) and the trace criterion. At trace ±2, all solutions are bounded exactly when the monodromy is ±I. | B, P |
| V | 28 | Formal Birkhoff normal form and the leading anharmonic frequency shift | A\*, P |
| V | 29 | Amplitude equation for driven, damped nonlinear resonance | P |
| V | 30 | Averaging in a rapidly driven system, effective potential, and error bounds | P, D |
| VI · Rigid bodies | 31 | Angular velocity and the rigid velocity field | A |
| VI | 32 | Inertia tensor, principal axes, and the parallel-axis theorem | A |
| VI | 33 | Angular momentum and precession of the symmetric top | A, B |
| VI | 34 | Rigid-body equations and their Lie–Poisson formulation in Hamiltonian models | A, C |
| VI | 35 | Euler-angle coordinates and the kinetic energy in those coordinates | A\* |
| VI | 36 | Euler's equations from the body-frame Lie–Poisson bracket | A\* |
| VI | 37 | Integrals, principal-axis stability, and elliptic-function solutions for the asymmetric top | A\*, D |
| VI | 38 | Holonomic constraints via ideals and the separate treatment of nonholonomic contact | B |
| VI | 39 | Rotating-frame Hamiltonian, Coriolis force, and centrifugal force | A\* |
| VII · Canonical mechanics | 40 | The regular Legendre transform and Hamilton's equations | B |
| VII | 41 | Partial Legendre transform and the Routhian | B |
| VII | 42 | Poisson brackets, Jacobi, and conversion between sign conventions | A |
| VII | 43 | Boundary derivatives of the action along families of solutions | B |
| VII | 44 | Maupertuis reparametrization and the Jacobi metric | A, B |
| VII | 45 | Canonical maps, generating functions, and symplectic evolution | A, B |
| VII | 46 | Preservation of the symplectic form and phase-space volume | A, B |
| VII | 47 | Hamilton–Jacobi equation and complete integrals | A, B |
| VII | 48 | Separated solutions in spherical, parabolic, and elliptic coordinates | A\* |
| VII | 49 | Action integral and an adiabatic estimate with explicit hypotheses | D, P |
| VII | 50 | Action–angle coordinates in one degree of freedom | B |
| VII | 51 | Exponentially small drift of a suitably corrected adiabatic invariant under analytic hypotheses | P, D |
| VII | 52 | Liouville–Arnold theorem, invariant tori, and degenerate cases | D |

## Electrodynamics

Volume 2, *The Classical Theory of Fields*, fourth edition, supplies the relativistic and vacuum field theory. Volume 8, *Electrodynamics of Continuous Media*, second edition, supplies macroscopic electromagnetism in matter. [Volume 2 contents](https://shop.elsevier.com/books/the-classical-theory-of-fields/landau/978-0-08-025072-4) · [Volume 8 contents](https://www.sciencedirect.com/book/monograph/9780080302751/electrodynamics-of-continuous-media)

| Landau–Lifshitz reference | Candidate formalization topics |
| --- | --- |
| Vol. 2, Ch. I–II | Lorentz transformations and relativistic particle mechanics as prerequisites |
| Vol. 2, Ch. III–IV | Charged-particle action, electromagnetic field tensor, Maxwell equations, and conservation laws |
| Vol. 2, Ch. V–VII | Static fields, vacuum waves, and optics |
| Vol. 2, Ch. VIII–IX | Fields of moving charges and radiation |
| Vol. 8 | Macroscopic Maxwell equations, constitutive relations, and propagation in matter |

## Later Topics

These are subject references for future proof plans. [Elsevier series catalogue](https://legacyfileshare.elsevier.com/assets/pdf_file/0006/796479/Landau_CTP_180529.pdf)

| Subject | Landau–Lifshitz reference |
| --- | --- |
| Gravitation and relativistic cosmology | Vol. 2, *The Classical Theory of Fields*, Ch. X–XIV |
| Nonrelativistic quantum mechanics | Vol. 3, *Quantum Mechanics* |
| Quantum electrodynamics | Vol. 4, *Quantum Electrodynamics* |
| Statistical physics and its connection to thermodynamics | Vol. 5, *Statistical Physics*, Part 1 |
| Fluid mechanics | Vol. 6, *Fluid Mechanics* |
| Elasticity | Vol. 7, *Theory of Elasticity* |
| Quantum statistical physics | Vol. 9, *Statistical Physics*, Part 2 |
| Kinetic theory and transport | Vol. 10, *Physical Kinetics* |

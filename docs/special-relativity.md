# Minkowski geometry and relativistic kinematics

This is the implemented foundation for README §3.1 and
[issue #40](https://github.com/MGYamada/ProjectAInos/issues/40).
[Electrodynamics #8](https://github.com/MGYamada/ProjectAInos/issues/8) consumes
its form calculus and observer decomposition. Particle actions and equations
of motion belong to §3.2; charged-particle actions also require the shared
variational foundation tracked by #7. Maxwell's equations are not premises or
conclusions of this geometry library.

## Conventions and layers

The physics layer uses natural units `c = 1` and `(-+++)`.
`SpecialRelativity.metric` and `spacetimeManifold` choose `.timeNegative`.
The common APIs `minkowskiForm σ d`, `LorentzMetric σ d M`, and
`LorentzManifold σ d` always receive a `LorentzConvention` explicitly:

| Convention | Time sign s | Metric | Negative directions q |
|---|---:|---|---:|
| `timePositive` | +1 | `(+,-,…,-)` | d |
| `timeNegative` | −1 | `(-,+,…,+)` | 1 |

`MinkowskiModel d` remains `Fin (d+1) → ℝ`. `Minkowski.space` takes values in
`EuclideanSpace ℝ (Fin d)`. Only its Euclidean norm represents spatial length;
the norm of the ambient coordinate-function space does not.

The common normalized pairing and quadratic form are

\[
\operatorname{pair}(v,w)=v^0w^0-\langle\mathbf v,\mathbf w\rangle,
\qquad Q(v)=s_\sigma g_\sigma(v,v)=(v^0)^2-\|\mathbf v\|^2.
\]

`intervalQuadratic_convention` proves this equality. Metric negation uses
`LorentzMetric.opposite` and `LorentzManifold.opposite`, preserving symmetry,
nondegeneracy, smoothness and local Minkowski coordinates. The underlying
C∞ scheme is unchanged. General Lorentz manifolds require no global frame,
and local Minkowski coordinates remain a predicate, not a general premise.

## Proof map

Paths in this table are relative to `ProjectAInos/`.

| Stage | Modules | Main public results |
|---|---|---|
| 1 | `SmoothGeometry/Minkowski/{Convention,Basic,Dual}`, `SmoothGeometry/Lorentzian` | Explicit signs, normalized Q, metric negation, continuous `flat`/`sharp` inverses |
| 2 | `SmoothGeometry/Minkowski/{Causal,Isometry,Matrix,Affine}` | Convex future cone, affine causal partial order, Lorentz subgroup and matrix identities, determinant ±1, proper/orthochronous subgroups, translated Poincaré maps and scheme isomorphisms |
| 3 | `SmoothGeometry/Minkowski/{Observer,Reflection,ReflectionDeterminant}`, `SpecialRelativity/{Boost,Velocity,Rapidity}` | Rest-space positivity and dimension, unique observer split, passive boosts and inverse, future preservation, velocity-ball action and collinear composition |
| 4 | `SpecialRelativity/ProperTime` | Local integrability, Poincaré and reparameterization invariance, null proper time, unit four-velocity, inertial time dilation |
| 5 | `SmoothGeometry/DifferentialForm/{Flat,Exterior,Coordinates,Calculus,Naturality}` | Open-domain locality, d²=0, wedge normalization, graded Leibniz, pullback composition, d/pullback and wedge/pullback compatibility |
| 6 | `SmoothGeometry/DifferentialForm/{Hodge,HodgeBasis}`, `SmoothGeometry/Minkowski/{Hodge,HodgeNaturality,HodgeFour,TwoForm}` | Wedge-normalized Hodge, mathlib comparison, square/sign/naturality, six coordinate signs, observer reconstruction |
| Examples | `SpecialRelativity/{Examples,FormExamples}` | Nonzero boost and inverse, subluminality, clock rate, nonzero exact field and gauge identity |

All shared modules are independent of `SpecialRelativity`. Every library
module is imported by `ProjectAInos.lean`.

## Causality, symmetry and observers

`Timelike`, `Spacelike`, and `Lightlike` mean respectively `Q > 0`, `Q < 0`,
and `v ≠ 0 ∧ Q = 0`. `Causal` includes zero. `FutureCausal` is the closed cone
`‖space v‖ ≤ time v`; every nonzero member has positive time component.
`CausallyPrecedes p q` uses the affine displacement `q -ᵥ p`, and is reflexive,
transitive and antisymmetric. `intervalSq σ p q` is the signed metric interval;
it is distinct from Q.

`LorentzGroup d` is a subgroup of linear equivalences preserving `pair`.
`mem_lorentzGroup_iff σ` identifies it with the isometries of either metric.
The matrix API proves `Lᵀ g L = g` and `det L = ±1`. Proper transformations
have determinant +1. Orthochronous transformations preserve the future cone;
this is separate from spacetime orientation. `flat_natural` uses the inverse
Lorentz map on covectors, whereas vectors transform by the map itself.

`PoincareGroup.ofLinearTranslation L a` constructs `v ↦ L v + a` as an affine
isometry, including pure translations. `toSchemeIso` uses
`Manifold.schemeMap` and its composition laws for the corresponding smooth
scheme automorphism.

An `Observer d` has future-directed velocity u with `Q(u)=1`. Its `clock` is
`θᵤ(v)=pair(u,v)=sσ gσ(u,v)`. `restSpace` is the kernel of this functional,
`project` removes `θᵤ(v)u`, and `split` is a linear equivalence
`V ≃ ℝ × restSpace`. The rest space has dimension d, and its metric
`-pair = -sσ gσ` is positive definite. Clock and projection commute with
orthochronous transformations.

## Boosts, velocity and proper time

`Velocity d` is the Euclidean open unit ball. `boost β` is defined at zero
velocity as well as at nonzero velocity, using two metric reflections. Its
proved coordinate formula is the passive transformation

\[
t'=\gamma(t-\boldsymbol\beta\cdot\mathbf x),\qquad
\mathbf x'=\mathbf x+
\left(\frac{\gamma^2}{1+\gamma}\boldsymbol\beta\cdot\mathbf x-\gamma t\right)
\boldsymbol\beta.
\]

The factor has no division by `‖β‖²`. The boost is proper and orthochronous;
`boost_neg_inverse` proves its inverse. Future unit observers are equivalent
to velocities. This supplies a `MulAction` of the orthochronous Lorentz group
on the velocity ball and proves that transformed speeds remain below one.
`transform_collinear` gives `(a-b)/(1-ba)` for a passive boost;
`rapidity_add` gives the additive `artanh` law for `(a+b)/(1+ab)`.
No theorem identifies a product of non-collinear boosts with a single boost.

`properTime γ a b` is the interval integral of `sqrt (Q (deriv γ t))`.
`TimelikeSegment γ a b` records `a ≤ b`, C¹ regularity in a neighbourhood
of every point of the closed interval, and future timelike derivatives.
The integral is total as a Lean definition; its physical interpretation uses
these hypotheses. Integrability needs the local C¹ condition.

Poincaré invariance only needs differentiability on the interval.
`properTime_reparametrize` assumes C¹ regularity of f near each source point
and of γ near its image, and `deriv f ≥ 0` on the interval. It therefore
includes orientation-preserving C¹ reparameterizations and proves equality
with the integral between `f a` and `f b`. `fourVelocity_unit` and
`fourVelocity_metric` require a timelike tangent and prove Q=1 and g(U,U)=−1.
Null proper time is proved separately by `properTime_null`; no null
four-velocity normalization theorem is asserted.

## Flat forms and Hodge normalization

`Form E k := E → E [⋀^Fin k]→L[ℝ] ℝ` is metric independent.
`exteriorDerivative` reuses mathlib's `extDeriv`. The calculus on open domains
uses regularity and equalities on the domain; locality and restriction
lemmas remove dependence on ambient extensions. Pullbacks use `fderiv`, with
explicit differentiability hypotheses in their laws. Interior product inserts
the vector into the first slot.

For finite coordinate spaces, `toExterior` identifies continuous alternating
forms with `Λᵏ E*` through the determinant pairing. `wedgeFiber` and `wedge`
use this proved equivalence, and `wedge_one_one` fixes
`(a ∧ b)(v,w) = a(v)b(w) - a(w)b(v)`. The graded Leibniz theorem is expressed
in the full exterior algebra, where all terms have degree k+l+1, avoiding
casts between different parenthesizations of this degree. The equality is
proved at each point under differentiability there.

`SpacetimeOrientation.standard` means `dt ∧ dx ∧ dy ∧ dz` in four dimensions;
`reversed` is the opposite orientation. `hodgeFiber` and `hodgeForm` receive
both orientation and signature explicitly, with `hkl : k+l=d+1`.
`hodgeFiber_pairing` proves the defining equation

\[
\alpha\wedge\star\beta=\langle\alpha,\beta\rangle_{g^{-1}}\operatorname{vol}.
\]

The implementation uses the perfect wedge pairing and the inverse metric.
`hodge_eq_mathlib_inverse` proves that this normalization equals
`(-1)^(k*l)` times the inverse of mathlib's opposite-degree Hodge map.
The exterior-power map is transported to continuous forms through
`toExterior_hodgeFiber`, not identified without proof.

The proved laws are `star² = (-1)^(k*l+q)`, reversal of orientation changing
star's sign, and `star_{-g} = (-1)^k star_g` for the same orientation.
`hodgeFiber_pullback` and `hodgeForm_pullback` prove compatibility with proper
Lorentz pullbacks. In four dimensions on two-forms, `star² = -1` and
`star_{-g} = star_g`. All six basis signs are checked; in particular,

\[
\star(dt\wedge dx)=-dy\wedge dz,\qquad
\star(dy\wedge dz)=dt\wedge dx.
\]

For an observer u, `reconstructTwoForm_contractions` proves

\[
F=\theta_u\wedge\iota_u F-\star(\theta_u\wedge\iota_u\star F).
\]

It works for both signatures and orientations, and for arbitrary u and F
satisfying the bundled observer hypotheses. This is #8's entry point for
electric/magnetic decomposition; sign conventions for naming those physical
fields remain with electrodynamics. `coordinateField_reconstruction` applies
it to the nonzero field `d(t dx) = dt ∧ dx`. The gauge check allows any C²
zero-form χ and proves `d(A+dχ)=dA`.

Forms and Hodge on curved manifolds, connections and curvature remain later
extensions. No global-frame assumption is added to the manifold interface.

## Verification

The required **Lean build** CI job builds with warnings as errors, checks root
imports and public consumer APIs, and audits transitive axiom dependencies.
The local counterparts are:

```sh
lake build --wfail ProjectAInos
lake exe mk_all --check --lib ProjectAInos
lake env lean -DwarningAsError=true checks/SmoothGeometryAPI.lean
lake env lean -DwarningAsError=true checks/SpecialRelativityAPI.lean
lake env lean -DwarningAsError=true checks/AxiomAudit.lean
```

The public API checks use default elaborator options. Exact examples distinguish
timelike, spacelike, lightlike and zero vectors; use velocity 3/5, factor 5/4
and clock rate 4/5; and check the nonzero field and Hodge signs. The axiom
allowlist is `propext`, `Classical.choice`, `Quot.sound`. No additional axioms
or unfinished proofs are used.

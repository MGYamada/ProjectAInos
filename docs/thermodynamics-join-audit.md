# Thermal-join assumptions and a populated model

`ThermalFamily` is a family of geometrically regular simple systems, closed
under positive scaling and thermal joining. Its comparison and calibration
theorems use A1–A7 and S1–S3 for the admitted systems, including the joins,
together with the stated T1–T4 data. Contact, splitting, the zeroth law, and
transversality by themselves are not advertised as supplying joined-system
geometric regularity.

This audit addresses the distinction raised in
[issue #12](https://github.com/MGYamada/ProjectAInos/issues/12) and the populated
model requested in [issue #10](https://github.com/MGYamada/ProjectAInos/issues/10).
The [physical development](thermodynamics-physical.md) gives the full proof
chain and public entropy endpoints.

## The contact layer and the geometric layer

The weaker `ThermalJoin` type in
[PhysicalComparison.lean](../ProjectAInos/Thermodynamics/PhysicalComparison.lean)
requires only:

1. A represented state at each coordinate in the joined domain.
2. Accessibility from a constituent pair to its total-energy joined state.
3. A reverse-accessible split of every joined state, preserving total energy
   and the individual work coordinates.

It does not require the joined domain to have a pressure field, unique
support, or any boundary regularity. `ThermalJoin.Equilibrium` defines
reversible contact at this layer. `ThermalJoin.entropy_maximum` proves the
maximum-entropy consequence of equilibrium when an additive monotone entropy
is supplied, without adding a joined `SimpleSystem`.

`SimpleThermalJoin` in
[ThermalFamily.lean](../ProjectAInos/Thermodynamics/ThermalFamily.lean) adds a
complete `SimpleSystem` in the canonical coordinates

$$
(U,V_1,V_2)\longmapsto (U,V_1\mathbin{\|}V_2),
$$

plus exact equalities for its domain and its representation of joined points.
`ThermalFamily.join_admitted` places this system back in the admitted family.
It therefore also receives T4, further joins, and positive scaled copies.
The weaker contact type remains available for models that do not justify
these geometric premises. There is no automatic promotion from arbitrary
contact data to a `SimpleThermalJoin`.

The original T1 says that the thermal join is itself a simple system. Thus
using S1–S3 on that join is part of the chosen simple-system interpretation,
not a consequence of the contact inequality alone.
[Lieb–Yngvason, Section IV, T1](https://arxiv.org/html/cond-mat/9708200v2)

## Field-by-field audit

Here $\Gamma_i\subseteq\mathbb R\times\mathbb R^{n_i}$ are the constituent
domains, and

$$
\Delta_{12}=\{(U,V_1,V_2):\exists U_1,U_2,
\ U=U_1+U_2,\ (U_i,V_i)\in\Gamma_i\}.
$$

“Derivable” in the table describes the mathematical dependence. Unless a
specific theorem is named, the generic `SimpleThermalJoin` constructor still
asks the model author to supply the corresponding `SimpleSystem` field. The
reservoir construction below proves every field for an actual model.

| Joined-system field | Dependence and current interface |
| --- | --- |
| `domain` and `domain_eq` | Fixed by the total-energy/concatenated-work construction; equality with the canonical image is explicit. |
| `isOpen_domain` | Inherited at the coordinate level: the join is the image of the open product domain under the surjective linear map that adds energies and retains both work vectors. Such a finite-dimensional map is open. The generic constructor stores the proof as a field. |
| `convex_domain` | Inherited at the coordinate level: a linear image of the convex product domain is convex. The generic constructor stores the proof as a field. |
| `represent` and `represent_eq` | Physical representation data, compatible with the contact-layer representation at every canonical joined point. Coordinates alone do not determine accessibility. |
| `mixing` (A7) | Derivable from coordinate-preserving splitting, component A7, composition/scaling consistency, and contact. It remains an explicit field of the joined `SimpleSystem`. |
| `irreversible` (S1) | Derivable from a split, component S1, contact, and spectator cancellation. It remains an explicit field of the joined `SimpleSystem`. |
| `pressure` | A chosen finite-slope field on the joined coordinate domain. It is not obtained by merely concatenating the component pressure functions. |
| `pressure_support` | Additional joined-system S2 input in this interface: the normalized pressure form or its negative supports the joined forward sector. |
| `unique_support` | Additional joined-system S2 input: all supporting forms at the anchor have the same kernel. Reversible splitting alone supplies no proof of this property. |
| `pressure_locallyLipschitz` | Additional joined-system regularity input. Component regularity is not used as an automatic preservation theorem for arbitrary joins. |
| `boundary_pathConnected` | Additional joined-system S3 input on the boundary relative to its open domain. Connectedness of the whole domain does not substitute for this boundary premise. |

The two derivable physical fields have short arguments. To mix two joined
states, reversibly split each, regroup their scaled components, apply A7 in
each constituent, and make thermal contact again. Coordinate preservation
identifies the result with the joined coordinate convex combination. To
produce an irreversible successor of a joined state, split it as $x+y$,
replace $x$ by a strict successor $x'$, and join $x'+y$. Reverse accessibility
of the new join would imply $x'+y\preceq x+y$, contradicting cancellation and
the strictness of $x\preceq x'$.

S2 and S3 remain visible rather than being hidden in a theorem named only for
thermal contact. S2 concerns kernels of supporting forms, so it does not
silently fix a normal's sign. S3 is path-connectedness of
$\Gamma\cap\operatorname{frontier}(A_x)$; the source calls it arcwise
connectedness. The boundary of the ambient equilibrium domain is excluded.
[Lieb–Yngvason, Section III, S2–S3](https://arxiv.org/html/cond-mat/9708200v2)

## Non-vacuity is a separate predicate

`ThermalFamily.Nontrivial` asserts that some admitted simple system has a
nonempty domain. `nontrivial_iff_exists_isState` identifies this with the
existence of an actual represented member state.

The predicate is not added to every theorem. For example, a comparison
theorem quantified over states is valid even when no states exist, while a
calibrator-existence theorem for a specified pair already assumes their
domains are nonempty. The new predicate distinguishes these conditional
results from a demonstration that their physical interface has a populated
model.

## The smooth reservoir family

[ReservoirModel.lean](../ProjectAInos/Thermodynamics/ReservoirModel.lean)
constructs such a model in the namespace `Physical.Reservoir`. The carrier is
`SectorState`, with coordinates $(s,r)$ for entropy and amount and order

$$
(s,r)\preceq(s',r')\quad\Longleftrightarrow\quad
r=r'\ \text{and}\ s\leq s'.
$$

`Reservoir.accessibility` supplies all A1–A6 fields using the existing sector
order and its stability proof. For every finite work dimension $n$ and amount
$r>0$, the admitted reservoir is

$$
\Gamma_n=\{(U,V):U>0\},\qquad
j_r(U,V)=(U,r),\qquad P(U,V)=0.
$$

`Reservoir.system` proves its A7/S1–S3 fields. Mixing is an equality of
energy–amount pairs. Increasing $U$ by one gives an irreversible successor.
`forwardSector_eq` and `relative_boundary_eq` calculate

$$
A_x=\{y:U_y\geq U_x\},\qquad
\partial_{\Gamma_n}A_x=\{y:U_y=U_x\}.
$$

The latter is a nonempty affine hyperplane, hence path-connected. Any
supporting functional vanishes on the work directions, because both positive
and negative work displacements remain in the sector. Its nonzero energy
coefficient then gives precisely the zero-pressure supporting kernel.
`unique_support` proves this directly. The constant pressure is locally
Lipschitz.

`Reservoir.scaled` realizes positive scaling by $t$ as the reservoir with
amount $tr$. The inverse coordinate scaling cancels the outer extensive
scaling, including in the representation equality required on the ambient
coordinate space. `Reservoir.join` gives the reservoir of dimension $n+m$
and amount $r+q$. `join_domain` verifies the exact domain image; any positive
total energy can, for example, be split into two positive halves. Contact
and equilibrium splitting are equalities of energy–amount pairs. Thus the
join is a concrete full `SimpleSystem`, not an unproved geometry premise in
this example.

`Reservoir.family` admits precisely positive-amount reservoirs. Its thermal
relation is universal. This satisfies the reversible-contact criterion
because every pair of reservoir states joins reversibly. Symmetry, the
zeroth law, and positive scaled-copy equilibrium follow. Transversality uses
the states at energies $U/2$ and $2U$ with the original work coordinates.

The following proofs exercise the populated interface:

| API | Witness or result |
| --- | --- |
| `Reservoir.system_nonempty` | An actual point $(1,0)$ in every reservoir domain |
| `Reservoir.family_nontrivial` | The admitted zero-work-coordinate reservoir of amount one is nonempty |
| `Reservoir.represented_state` | The raw state $(1,1)$ is represented in the family |
| `Reservoir.contact_equilibrium` | Arbitrary states of two reservoirs are in reversible contact |
| `Reservoir.exists_calibrator` | The general physical calibrator theorem instantiated for two nonempty reservoirs |
| `Reservoir.product_comparison` | The general finite-product theorem instantiated for this family |

The model permits arbitrary finite work dimension, including $n=0$; work
coordinates do not affect its entropy. It exhibits irreversible adiabatic
energy increases even though all states are thermally equivalent. It
therefore witnesses the universal-isotherm branch of the thermal argument.
It does not exercise the alternative with nonconstant thermal classes.

This is a model of `Accessibility`, `SimpleSystem`, and `ThermalFamily` on
`SectorState`. It is not an instantiation of `AtomicDomains` or of the
canonical finite-atom reaction endpoints. The existing ideal-gas composite
model has a different role: it witnesses the algebraic entropy–amount,
stability, completion, and conservation layer. Neither model is described
as a microscopic derivation of thermodynamics.

## Nonsmooth joins and phase transitions

The contact layer can express a join before support regularity is known.
For a proposed phase-coexistence or nonsmooth model, the route is to construct
that contact/splitting data first and then check the geometric fields needed
for `SimpleThermalJoin`. A corner with multiple supporting hyperplanes or a
pressure field failing local Lipschitz regularity does not satisfy the current
S2 interface. A boundary without the required relative path-connectedness
does not satisfy S3. The current comparison theorem is not a replacement for
those checks.

Nondifferentiability of the energy entropy alone is not automatically the
same as failure of these geometric assumptions: the implemented thermal
maximum criterion explicitly permits intervals of supporting slopes.
Conversely, those slope-interval results do not prove that every phase
transition model meets S2–S3. No general nonsmooth relaxation, preservation
theorem for arbitrary physical joins, or non-universal-temperature thermal
family is constructed here. The smooth reservoir witness and the conditional
entropy theorems have exactly the scopes stated above.

"""Exact electromagnetic convention and radial-reconstruction checks.

Time first, c=1, metric (-+++), orientation dt^dx^dy^dz. No random or
floating-point computations are used. These experiments supplement Lean.
"""

from itertools import product

import sympy as sp


def curvature(potential, coordinates):
    return sp.Matrix(4, 4, lambda i, j: sp.diff(potential[j], coordinates[i])
                     - sp.diff(potential[i], coordinates[j]))


def hodge(field):
    metric = sp.diag(-1, 1, 1, 1)
    raised = metric * field * metric
    return sp.Matrix(4, 4, lambda i, j: sum(
        sp.Rational(1, 2) * sp.LeviCivita(i, j, k, l) * raised[k, l]
        for k, l in product(range(4), repeat=2)))


def contraction(left, right):
    raised = sp.diag(-1, 1, 1, 1) * right * sp.diag(-1, 1, 1, 1)
    return sum(left[i, j] * raised[i, j] for i, j in product(range(4), repeat=2))


def check_zero(name, expression):
    entries = list(expression) if isinstance(expression, sp.MatrixBase) else [expression]
    if any(sp.simplify(entry) != 0 for entry in entries):
        raise AssertionError(f"{name}: exact residual is nonzero: {expression}")


def verify_virial_coulomb_larmor():
    """The virial identity, motion in a Coulomb field and Larmor's theorem (§§34, 39, 45).

    * §34: the improvement stress T^{mu nu} = (d^mu d^nu - eta^{mu nu} box) chi is symmetric
      and conserved, with spatial trace 3 d_0^2 chi - 2 Laplacian chi, and T^00 plus the
      four-trace is the spatial trace;
    * §39: for H = sqrt(m^2 + e^{-2s}(p_s^2 + p_phi^2)) + alpha e^{-s}, X = (p_phi^2 - alpha^2)
      e^{-s} + alpha H and Y = p_phi p_s e^{-s} have the brackets of CoulombMotion.lean, and
      d^2X/dphi^2 = -kappa^2 X with kappa^2 = 1 - alpha^2/p_phi^2 (the rosette);
    * §45: in the symmetric gauge, |p - (e/2) B x q|^2/2m = |p|^2/2m - Omega.(q x p)
      + (e^2/8m)|B x q|^2 with Omega = e B/2m.
    """
    coordinates = sp.symbols("t x y z", real=True)
    eta = sp.diag(-1, 1, 1, 1)
    chi = sp.Function("chi")(*coordinates)
    box = sum(eta[a, a] * sp.diff(chi, coordinates[a], 2) for a in range(4))
    stress = sp.Matrix(4, 4, lambda m, n: eta[m, m] * eta[n, n]
                       * sp.diff(chi, coordinates[m], coordinates[n]) - eta[m, n] * box)
    check_zero("improvement stress symmetry", stress - stress.T)
    check_zero("improvement stress conservation", sp.Matrix(
        [sum(sp.diff(stress[m, n], coordinates[m]) for m in range(4)) for n in range(4)]))
    spatial_trace = sum(stress[a, a] for a in range(1, 4))
    laplacian = sum(sp.diff(chi, coordinates[a], 2) for a in range(1, 4))
    check_zero("improvement spatial trace",
               spatial_trace - 3 * sp.diff(chi, coordinates[0], 2) + 2 * laplacian)
    check_zero("energy plus four-trace", stress[0, 0] + (-stress[0, 0] + spatial_trace)
               - spatial_trace)

    s, phi, ps, pphi = sp.symbols("s phi p_s p_phi", real=True)
    mass, alpha = sp.symbols("m alpha", positive=True)
    energy = sp.sqrt(mass**2 + sp.exp(-2 * s) * (ps**2 + pphi**2))
    hamiltonian = energy + alpha * sp.exp(-s)

    def bracket(f, g):
        return (sp.diff(f, s) * sp.diff(g, ps) - sp.diff(f, ps) * sp.diff(g, s)
                + sp.diff(f, phi) * sp.diff(g, pphi) - sp.diff(f, pphi) * sp.diff(g, phi))

    orbit_x = (pphi**2 - alpha**2) * sp.exp(-s) + alpha * hamiltonian
    orbit_y = pphi * ps * sp.exp(-s)
    check_zero("Coulomb bracket X", bracket(orbit_x, hamiltonian)
               + (pphi**2 - alpha**2) * ps * sp.exp(-3 * s) / energy)
    check_zero("Coulomb bracket Y", bracket(orbit_y, hamiltonian)
               - orbit_x * pphi * sp.exp(-2 * s) / energy)
    check_zero("Coulomb angular velocity", bracket(phi, hamiltonian)
               - pphi * sp.exp(-2 * s) / energy)
    check_zero("Coulomb angular momentum", bracket(pphi, hamiltonian))
    x_rate = bracket(orbit_x, hamiltonian) / bracket(phi, hamiltonian)
    y_rate = bracket(orbit_y, hamiltonian) / bracket(phi, hamiltonian)
    check_zero("rosette first equation", x_rate + (pphi**2 - alpha**2) * orbit_y / pphi**2)
    check_zero("rosette second equation", y_rate - orbit_x)

    q = sp.Matrix(sp.symbols("q0:3", real=True))
    p = sp.Matrix(sp.symbols("p0:3", real=True))
    field = sp.Matrix(sp.symbols("B0:3", real=True))
    charge = sp.symbols("e", real=True)
    kinetic = p - charge / 2 * field.cross(q)
    larmor = charge * field / (2 * mass)
    rotating = (p.dot(p)) / (2 * mass) - larmor.dot(q.cross(p))
    check_zero("Larmor identity", kinetic.dot(kinetic) / (2 * mass) - rotating
               - charge**2 / (8 * mass) * field.cross(q).dot(field.cross(q)))


def verify():
    t, x, y, z = coordinates = sp.symbols("t x y z", real=True)
    ex, ey, ez, bx, by, bz = sp.symbols("E_x E_y E_z B_x B_y B_z", real=True)
    field = sp.Matrix([[0, -ex, -ey, -ez], [ex, 0, bz, -by],
                       [ey, -bz, 0, bx], [ez, by, -bx, 0]])
    scalar = lambda f: sp.Rational(1, 2) * contraction(f, f)
    pseudo = lambda f: sp.Rational(1, 4) * contraction(f, hodge(f))
    check_zero("Hodge square", hodge(hodge(field)) + field)
    check_zero("B squared minus E squared", scalar(field)
               - (bx**2 + by**2 + bz**2 - ex**2 - ey**2 - ez**2))
    check_zero("E dot B", pseudo(field) - (ex * bx + ey * by + ez * bz))
    parity = sp.diag(1, -1, 1, 1)
    reflected = parity.T * field * parity
    check_zero("scalar under reflection", scalar(reflected) - scalar(field))
    check_zero("pseudoscalar under reflection", pseudo(reflected) + pseudo(field))
    check_zero("Hodge under reflection", hodge(reflected) + parity.T * hodge(field) * parity)

    rapidity = sp.symbols("rapidity", real=True)
    c, s = sp.cosh(rapidity), sp.sinh(rapidity)
    boost = sp.Matrix([[c, s, 0, 0], [s, c, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    boosted = boost.T * field * boost
    check_zero("scalar under boost", scalar(boosted) - scalar(field))
    check_zero("pseudoscalar under boost", pseudo(boosted) - pseudo(field))

    uniform_potential = sp.Matrix([0, -ex * t, 0, bx * y])
    uniform = curvature(uniform_potential, coordinates)
    check_zero("uniform potential signs", uniform - field.subs({ey: 0, ez: 0, by: 0, bz: 0}))
    gauge_function = t * x + y * z
    shifted = uniform_potential + sp.Matrix([sp.diff(gauge_function, q) for q in coordinates])
    check_zero("gauge curvature", curvature(shifted, coordinates) - uniform)
    for i, j, k in product(range(4), repeat=3):
        check_zero("Bianchi", sp.diff(uniform[j, k], coordinates[i])
                   + sp.diff(uniform[k, i], coordinates[j]) + sp.diff(uniform[i, j], coordinates[k]))

    linear = sp.zeros(4)
    linear[0, 1], linear[1, 0] = t, -t
    for degree, jet in [(0, field), (1, linear)]:
        potential = sp.Matrix([sum(coordinates[i] * jet[i, j] for i in range(4))
                               / sp.Integer(degree + 2) for j in range(4)])
        check_zero(f"radial gauge degree {degree}", sp.Matrix(coordinates).dot(potential))
        check_zero(f"radial reconstruction degree {degree}", curvature(potential, coordinates) - jet)
        wrong = sp.Matrix([sum(coordinates[i] * jet[i, j] for i in range(4))
                           / sp.Integer(degree + 1) for j in range(4)])
        if curvature(wrong, coordinates) == jet:
            raise AssertionError("radial check did not distinguish the wrong coefficient")

    tau = sp.symbols("tau", real=True)
    worldline = sp.Matrix([sp.sinh(tau), sp.cosh(tau), 0, 0])
    velocity, metric = worldline.diff(tau), sp.diag(-1, 1, 1, 1)
    force = metric * uniform.subs({ex: 1, bx: 0}) * velocity
    check_zero("proper-time mass shell", (velocity.T * metric * velocity)[0] + 1)
    check_zero("hyperbolic Lorentz force", velocity.diff(tau) - force)
    check_zero("force orthogonality", (velocity.T * metric * force)[0])
    verify_virial_coulomb_larmor()
    print("Electrodynamics exact checks passed: signs, invariants, covariance, gauge, "
          "Bianchi, degree 0/1 radial reconstruction, hyperbolic worldline, the virial "
          "improvement stress, the Coulomb brackets and rosette, and Larmor's identity.")


def main():
    verify()


if __name__ == "__main__":
    main()

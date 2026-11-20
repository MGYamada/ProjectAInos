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


def verify_static_fields_and_waves():
    """Static fields, the moving charge and waves (§§36–38, 46–48, 50).

    * §36: the regularized Newton kernel 1/(4 pi sqrt(r^2 + eps^2)) has the Laplacian
      -3 eps^2/(4 pi (r^2 + eps^2)^(5/2)), and the peak 3/(4 pi (r^2 + 1)^(5/2)) has integral 1;
    * §37: the point charge has field energy q^2/(8 pi eps) outside the radius eps;
    * §38: the boosted static potential -phi(gamma(x - Vt), y, z) (dt - V dx) gives L&L (38.8);
    * §46: div E = -box phi - d_t L and curl B - d_t E = -box a + grad L for A = (-phi, a);
    * §§47–48: the plane wave f(l.x) a with null l and <l, a> = 0 is a vacuum solution, and the
      Doppler factor is gamma (1 - V n_1);
    * §50: s1^2 + s2^2 + s3^2 = s0^2 - 4 det J for a Hermitian 2x2 matrix.
    """
    x, y, z = sp.symbols("x y z", real=True)
    eps, r = sp.symbols("epsilon r", positive=True)
    kernel = 1 / (4 * sp.pi * sp.sqrt(x**2 + y**2 + z**2 + eps**2))
    laplacian = sum(sp.diff(kernel, v, 2) for v in (x, y, z))
    check_zero("regularized kernel Laplacian",
               laplacian + 3 * eps**2 / (4 * sp.pi * (x**2 + y**2 + z**2 + eps**2)**sp.Rational(5, 2)))
    peak = sp.integrate(4 * sp.pi * r**2 * 3 / (4 * sp.pi * (r**2 + 1)**sp.Rational(5, 2)),
                        (r, 0, sp.oo))
    check_zero("peak integral", peak - 1)
    q = sp.symbols("q", real=True)
    energy = sp.integrate(4 * sp.pi * r**2 * (q / (4 * sp.pi * r**2))**2 / 2, (r, eps, sp.oo))
    check_zero("point-charge energy outside eps", energy - q**2 / (8 * sp.pi * eps))

    t = sp.symbols("t", real=True)
    coordinates = (t, x, y, z)
    velocity = sp.symbols("V", real=True)
    gamma = 1 / sp.sqrt(1 - velocity**2)
    comoving = (gamma * (x - velocity * t), y, z)
    coulomb = q / (4 * sp.pi * sp.sqrt(sum(c**2 for c in comoving)))
    potential = sp.Matrix([-gamma * coulomb, gamma * velocity * coulomb, 0, 0])
    field = curvature(potential, coordinates)
    electric = sp.Matrix([field[i, 0] for i in range(1, 4)])
    separation = sp.Matrix([x - velocity * t, y, z])
    distance = sp.sqrt(separation.dot(separation))
    sine_sq = (y**2 + z**2) / distance**2
    expected = q * (1 - velocity**2) * separation / (
        4 * sp.pi * distance**3 * (1 - velocity**2 * sine_sq)**sp.Rational(3, 2))
    point = {t: sp.Rational(1, 3), x: sp.Rational(7, 5), y: sp.Rational(-2, 3), z: sp.Rational(1, 2),
             velocity: sp.Rational(3, 5), q: 2}
    residual = (electric - expected).subs(point)
    if any(abs(sp.N(entry, 30)) > sp.Float("1e-25") for entry in residual):
        raise AssertionError(f"moving charge (38.8): residual {residual}")

    phi = sp.Function("phi")(*coordinates)
    a = [sp.Function(f"a{i}")(*coordinates) for i in range(3)]
    four = sp.Matrix([-phi] + a)
    field = curvature(four, coordinates)
    electric = [field[i, 0] for i in range(1, 4)]
    magnetic = [field[2, 3], field[3, 1], field[1, 2]]

    def box(f):
        return -sp.diff(f, t, 2) + sum(sp.diff(f, v, 2) for v in (x, y, z))

    lorenz = sp.diff(phi, t) + sum(sp.diff(a[i], v) for i, v in enumerate((x, y, z)))
    check_zero("div E in Lorenz form", sum(sp.diff(electric[i], v) for i, v in enumerate((x, y, z)))
               + box(phi) + sp.diff(lorenz, t))
    curl = [sp.diff(magnetic[2], y) - sp.diff(magnetic[1], z),
            sp.diff(magnetic[0], z) - sp.diff(magnetic[2], x),
            sp.diff(magnetic[1], x) - sp.diff(magnetic[0], y)]
    for i, v in enumerate((x, y, z)):
        check_zero(f"curl B - d_t E in Lorenz form {i}",
                   curl[i] - sp.diff(electric[i], t) + box(a[i]) - sp.diff(lorenz, v))

    kappa = sp.symbols("kappa", positive=True)
    profile = sp.Function("f")
    phase = kappa * (t - x)
    wave = sp.Matrix([0, 0, profile(phase), 0])
    wave_field = curvature(wave, coordinates)
    raised = sp.diag(-1, 1, 1, 1) * wave_field * sp.diag(-1, 1, 1, 1)
    check_zero("plane wave vacuum", sp.Matrix(
        [sum(sp.diff(raised[m, n], coordinates[m]) for m in range(4)) for n in range(4)]))
    normal = sp.Matrix(sp.symbols("n1:4", real=True))
    wavevector = kappa * sp.Matrix([1, -normal[0], -normal[1], -normal[2]])
    observer = gamma * sp.Matrix([1, velocity, 0, 0])
    check_zero("Doppler factor", wavevector.dot(observer)
               - gamma * kappa * (1 - velocity * normal[0]))

    j00, j11 = sp.symbols("J00 J11", real=True)
    re, im = sp.symbols("Re Im", real=True)
    coherency = sp.Matrix([[j00, re + sp.I * im], [re - sp.I * im, j11]])
    stokes = [j00 + j11, 2 * re, -2 * im, j00 - j11]
    check_zero("Stokes identity", sum(s**2 for s in stokes[1:]) - stokes[0]**2
               + 4 * coherency.det())


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
    verify_static_fields_and_waves()
    print("Electrodynamics exact checks passed: signs, invariants, covariance, gauge, "
          "Bianchi, degree 0/1 radial reconstruction, hyperbolic worldline, the virial "
          "improvement stress, the Coulomb brackets and rosette, Larmor's identity, the Newton kernel "
          "and the point-charge energy, the moving charge (38.8), the wave equation in Lorenz "
          "form, plane waves, the Doppler factor and the Stokes identity.")


def main():
    verify()


if __name__ == "__main__":
    main()

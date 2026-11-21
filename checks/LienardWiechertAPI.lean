/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.RetardedTime
import ProjectAinos.Electrodynamics.LienardWiechert
import ProjectAinos.Electrodynamics.LienardWiechertSource

/-! Public consumers of the Liénard–Wiechert potentials (Landau–Lifshitz §63): worldlines slower
than light with the uniform, rest and circular instances, the unique retarded time with its
smoothness and derivatives off the worldline, the potentials (63.4)–(63.5) with the Lorenz gauge,
the wave equation and the vacuum equations off the worldline, the fields (63.8)–(63.9) with their
light-cone forms, the comparison with the moving Coulomb field of §38, and the point charge as
the source of its field: the light-cone change of variables and the identity
`∫ φ box χ = −e ∫ χ(t, r(t)) dt` for test functions. Default elaborator options are intentional:
these checks must not rely on the implementation's transparency settings. Every statement is
pinned with its type. -/

noncomputable section


section RetardedTime

open Set Filter

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

example :
    Differentiable ℝ w.r :=
  differentiable_r w

example :
    ContDiff ℝ ∞ (deriv w.r) :=
  contDiff_deriv w

example :
    ContDiff ℝ ∞ (deriv (deriv w.r)) :=
  contDiff_deriv_deriv w

example (s₁ s₂ : ℝ) :
    ‖w.r s₂ - w.r s₁‖ ≤ w.v₀ * |s₂ - s₁| :=
  norm_sub_le w s₁ s₂

example (r₀ v : Space 3) (hv : ‖v‖ < 1) :
    SubluminalWorldline :=
  uniform r₀ v hv

example (r₀ v : Space 3) (hv : ‖v‖ < 1) (t : ℝ) :
    deriv (uniform r₀ v hv).r t = v :=
  deriv_uniform r₀ v hv t

example (r₀ : Space 3) :
    SubluminalWorldline :=
  rest r₀

example (ρ Ω : ℝ) (t : ℝ) :
    Space 3 :=
  circularPath ρ Ω t

example (ρ Ω t : ℝ) :
    HasDerivAt (circularPath ρ Ω)
      ((-(ρ * Ω) * Real.sin (Ω * t)) • EuclideanSpace.single 0 1 +
        (ρ * Ω * Real.cos (Ω * t)) • EuclideanSpace.single 1 1) t :=
  hasDerivAt_circularPath ρ Ω t

example (ρ Ω t : ℝ) :
    ‖deriv (circularPath ρ Ω) t‖ = |ρ * Ω| :=
  norm_deriv_circularPath ρ Ω t

example (ρ Ω : ℝ) (h : |ρ * Ω| < 1) :
    SubluminalWorldline :=
  circular ρ Ω h

example (t : ℝ) (x : Space 3) :
    ∃! τ : ℝ, t - τ = ‖x - w.r τ‖ :=
  existsUnique_retardedTime w t x

example (t : ℝ) (x : Space 3) :
    ℝ :=
  retardedTime w t x

example (t : ℝ) (x : Space 3) :
    t - w.retardedTime t x = ‖x - w.r (w.retardedTime t x)‖ :=
  sub_retardedTime w t x

example {t s : ℝ} {x : Space 3} :
    w.retardedTime t x = s ↔ t - s = ‖x - w.r s‖ :=
  retardedTime_eq_iff w

example (t : ℝ) (x : Space 3) :
    w.retardedTime t x ≤ t :=
  retardedTime_le w t x

example {t : ℝ} {x : Space 3} :
    w.retardedTime t x < t ↔ x ≠ w.r t :=
  retardedTime_lt_iff w

example (t : ℝ) :
    w.retardedTime t (w.r t) = t :=
  retardedTime_self w t

example (τ : ℝ) (y : Space 3) :
    w.retardedTime (τ + ‖y‖) (w.r τ + y) = τ :=
  retardedTime_add_norm w τ y

example (t : ℝ) (x : Space 3) :
    Space 3 :=
  retardedSeparation w t x

example (t : ℝ) (x : Space 3) :
    Space 3 :=
  retardedVelocity w t x

example (t : ℝ) (x : Space 3) :
    Space 3 :=
  retardedAcceleration w t x

example (t : ℝ) (x : Space 3) :
    Space 3 :=
  retardedDirection w t x

example (t : ℝ) (x : Space 3) :
    ℝ :=
  retardedDenominator w t x

example (t : ℝ) (x : Space 3) :
    ‖w.retardedSeparation t x‖ = t - w.retardedTime t x :=
  norm_retardedSeparation w t x

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    w.retardedSeparation t x ≠ 0 :=
  retardedSeparation_ne_zero w h

example (t : ℝ) (x : Space 3) :
    ‖w.retardedVelocity t x‖ ≤ w.v₀ :=
  norm_retardedVelocity_le w t x

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    ‖w.retardedDirection t x‖ = 1 :=
  norm_retardedDirection w h

example (t : ℝ) (x : Space 3) :
    (1 - w.v₀) * ‖w.retardedSeparation t x‖ ≤ w.retardedDenominator t x :=
  mul_norm_le_retardedDenominator w t x

example (t : ℝ) (x : Space 3) :
    w.retardedDenominator t x ≤ (1 + w.v₀) * ‖w.retardedSeparation t x‖ :=
  retardedDenominator_le_mul_norm w t x

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    0 < w.retardedDenominator t x :=
  retardedDenominator_pos w h

example (t : ℝ) (x : Space 3) :
    w.retardedDenominator t x = ‖w.retardedSeparation t x‖ *
      (1 - inner ℝ (w.retardedDirection t x) (w.retardedVelocity t x)) :=
  retardedDenominator_eq_mul w t x

example (τ : ℝ) (y : Space 3) :
    w.retardedSeparation (τ + ‖y‖) (w.r τ + y) = y :=
  retardedSeparation_add_norm w τ y

example (τ : ℝ) (y : Space 3) :
    w.retardedVelocity (τ + ‖y‖) (w.r τ + y) = deriv w.r τ :=
  retardedVelocity_add_norm w τ y

example (τ : ℝ) (y : Space 3) :
    w.retardedAcceleration (τ + ‖y‖) (w.r τ + y) = deriv (deriv w.r) τ :=
  retardedAcceleration_add_norm w τ y

example (τ : ℝ) (y : Space 3) :
    w.retardedDenominator (τ + ‖y‖) (w.r τ + y) = ‖y‖ - inner ℝ y (deriv w.r τ) :=
  retardedDenominator_add_norm w τ y

example (t : ℝ) (x : Space 3) :
    w.retardedTime t x + ‖w.retardedSeparation t x‖ = t :=
  retardedTime_add_norm_retardedSeparation w t x

example (t : ℝ) (x : Space 3) :
    w.r (w.retardedTime t x) + w.retardedSeparation t x = x :=
  r_add_retardedSeparation w t x

example :
    ℝ × Space 3 ≃ ℝ × Space 3 :=
  lightConeEquiv w

example (q : (ℝ × Space 3) × ℝ) :
    ℝ :=
  lagEquation w q

example {q : (ℝ × Space 3) × ℝ} (hq : q.1.2 - w.r q.2 ≠ 0) :
    ContDiffAt ℝ ∞ w.lagEquation q :=
  contDiffAt_lagEquation w hq

example (p : ℝ × Space 3) {s : ℝ} (hs : p.2 - w.r s ≠ 0) :
    HasDerivAt (fun s => w.lagEquation (p, s))
      (-1 + ‖p.2 - w.r s‖⁻¹ * inner ℝ (p.2 - w.r s) (deriv w.r s)) s :=
  hasDerivAt_lagEquation w p hs

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) :=
  contDiffAt_retardedTime w h

example :
    IsOpen {p : ℝ × Space 3 | p.2 ≠ w.r p.1} :=
  isOpen_offWorldline_prod w

example :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2)
      {p : ℝ × Space 3 | p.2 ≠ w.r p.1} :=
  contDiffOn_retardedTime w

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    HasFDerivAt (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2)
      ((w.retardedDenominator t x)⁻¹ •
        (‖w.retardedSeparation t x‖ • ContinuousLinearMap.fst ℝ ℝ (Space 3) -
          (innerSL ℝ (w.retardedSeparation t x)).comp (ContinuousLinearMap.snd ℝ ℝ (Space 3))))
      (t, x) :=
  hasFDerivAt_retardedTime w h

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) (1, 0) =
      ‖w.retardedSeparation t x‖ / w.retardedDenominator t x :=
  fderiv_retardedTime_time w h

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) (k : Space 3) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) (0, k) =
      -inner ℝ (w.retardedSeparation t x) k / w.retardedDenominator t x :=
  fderiv_retardedTime_space w h k

example {t : ℝ} {x : Space 3} (h : x ≠ w.r t) (k : Space 3) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (t, x) (0, k) =
      -inner ℝ (w.retardedDirection t x) k /
        (1 - inner ℝ (w.retardedDirection t x) (w.retardedVelocity t x)) :=
  fderiv_retardedTime_space_direction w h k

example :
    Set Spacetime :=
  offWorldline w

example :
    IsOpen w.offWorldline :=
  isOpen_offWorldline w

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (fun z : Spacetime => w.retardedTime (z 0) (space z)) y :=
  contDiffAt_retardedTime_spacetime w hy

example :
    ContDiffOn ℝ ∞ (fun z : Spacetime => w.retardedTime (z 0) (space z)) w.offWorldline :=
  contDiffOn_retardedTime_spacetime w

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasFDerivAt (fun z : Spacetime => w.retardedTime (z 0) (space z))
      ((w.retardedDenominator (y 0) (space y))⁻¹ •
        (‖w.retardedSeparation (y 0) (space y)‖ • (time : Spacetime →L[ℝ] ℝ) -
          (innerSL ℝ (w.retardedSeparation (y 0) (space y))).comp
            (space : Spacetime →L[ℝ] Space 3))) y :=
  hasFDerivAt_retardedTime_spacetime w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    partialAt (fun z : Spacetime => w.retardedTime (z 0) (space z)) 0 y =
      ‖w.retardedSeparation (y 0) (space y)‖ / w.retardedDenominator (y 0) (space y) :=
  partialAt_retardedTime_zero w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    partialAt (fun z : Spacetime => w.retardedTime (z 0) (space z)) i.succ y =
      -w.retardedSeparation (y 0) (space y) i / w.retardedDenominator (y 0) (space y) :=
  partialAt_retardedTime_succ w hy i

end SubluminalWorldline

end ProjectAinos.Electrodynamics

end RetardedTime

section LienardWiechert

open Set Filter

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

namespace LienardWiechert

example (f : Spacetime → ℝ) (a : ℝ) (b : Space 3) (y : Spacetime) :
    Prop :=
  HasGradAt f a b y

example {f : Spacetime → ℝ} {L : Spacetime →L[ℝ] ℝ} {a : ℝ} {b : Space 3} {y : Spacetime}
    (hf : HasFDerivAt f L y) (hL : ∀ δ : Spacetime, L δ = a * δ 0 + inner ℝ b (space δ)) :
    HasGradAt f a b y :=
  HasGradAt.of_hasFDerivAt hf hL

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (δ : Spacetime) :
    fderiv ℝ f y δ = a * δ 0 + inner ℝ b (space δ) :=
  HasGradAt.apply hf δ

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y) :
    DifferentiableAt ℝ f y :=
  HasGradAt.differentiableAt hf

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y) :
    partialAt f 0 y = a :=
  HasGradAt.partialAt_zero hf

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (i : Fin 3) :
    partialAt f i.succ y = b i :=
  HasGradAt.partialAt_succ hf i

example {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (hg : HasGradAt g c d y) :
    HasGradAt (fun z => f z + g z) (a + c) (b + d) y :=
  HasGradAt.add hf hg

example {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (hg : HasGradAt g c d y) :
    HasGradAt (fun z => f z - g z) (a - c) (b - d) y :=
  HasGradAt.sub hf hg

example {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (hg : HasGradAt g c d y) :
    HasGradAt (fun z => f z * g z) (f y * c + g y * a) (f y • d + g y • b) y :=
  HasGradAt.mul hf hg

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (k : ℝ) (hf : HasGradAt f a b y) :
    HasGradAt (fun z => k * f z) (k * a) (k • b) y :=
  HasGradAt.const_mul k hf

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} {h : ℝ → ℝ} {h' : ℝ}
    (hh : HasDerivAt h h' (f y)) (hf : HasGradAt f a b y) :
    HasGradAt (fun z => h (f z)) (h' * a) (h' • b) y :=
  HasGradAt.comp hh hf

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y) :
    HasGradAt (fun z => -f z) (-a) (-b) y :=
  HasGradAt.neg hf

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (h0 : f y ≠ 0) :
    HasGradAt (fun z => (f z)⁻¹) (-(f y ^ 2)⁻¹ * a) (-(f y ^ 2)⁻¹ • b) y :=
  HasGradAt.inv hf h0

example (y : Spacetime) :
    HasGradAt (fun z => z 0) 1 0 y :=
  hasGradAt_time y

example (i : Fin 3) (y : Spacetime) :
    HasGradAt (fun z => z i.succ) 0 (EuclideanSpace.single i 1) y :=
  hasGradAt_coord i y

example (f g : Spacetime → ℝ) (y : Spacetime) :
    ℝ :=
  gradPairing f g y

example {f g : Spacetime → ℝ} {a c : ℝ} {b d : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    (hg : HasGradAt g c d y) :
    LienardWiechert.gradPairing f g y = -(a * c) + inner ℝ b d :=
  HasGradAt.gradPairing hf hg

example {f : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y) :
    ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ f z :=
  eventually_differentiableAt hf

example {f : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y) (μ : Fin 4) :
    DifferentiableAt ℝ (partialAt f μ) y :=
  differentiableAt_partialAt hf μ

example {f g : Spacetime → ℝ} {y : Spacetime} (h : f =ᶠ[𝓝 y] g) :
    box f y = box g y :=
  box_congr h

example (μ : Fin 4) (y : Spacetime) :
    box (fun z => z μ) y = 0 :=
  box_coord μ y

example (k : ℝ) {f : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y) :
    box (fun z => k * f z) y = k * box f y :=
  box_const_mul k hf

example {f g : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y) :
    box (fun z => f z - g z) y = box f y - box g y :=
  box_sub hf hg

example {ι : Type*} (s : Finset ι) {f : ι → Spacetime → ℝ} {y : Spacetime}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y) :
    box (fun z => ∑ i ∈ s, f i z) y = ∑ i ∈ s, box (f i) y :=
  box_sum s hf

example {f g : Spacetime → ℝ} {y : Spacetime} (hf : ContDiffAt ℝ 2 f y) (hg : ContDiffAt ℝ 2 g y) :
    box (fun z => f z * g z) y = f y * box g y + g y * box f y + 2 * gradPairing f g y :=
  box_mul hf hg

example {f : Spacetime → ℝ} {y : Spacetime} {h h' : ℝ → ℝ} {h'' : ℝ} (hf : ContDiffAt ℝ 2 f y)
    (hh : ∀ᶠ s in 𝓝 (f y), HasDerivAt h (h' s) s) (hh' : HasDerivAt h' h'' (f y)) :
    box (fun z => h (f z)) y = h'' * gradPairing f f y + h' (f y) * box f y :=
  box_comp hf hh hh'

variable (w : SubluminalWorldline)

example (y : Spacetime) :
    ℝ :=
  tau w y

example (y : Spacetime) :
    Space 3 :=
  sep w y

example (y : Spacetime) :
    Space 3 :=
  vel w y

example (y : Spacetime) :
    Space 3 :=
  acc w y

example (y : Spacetime) :
    ℝ :=
  denom w y

example (y : Spacetime) :
    ℝ :=
  kfac w y

example (y : Spacetime) :
    ‖sep w y‖ = y 0 - tau w y :=
  norm_sep w y

example (y : Spacetime) :
    denom w y = (y 0 - tau w y) - inner ℝ (sep w y) (vel w y) :=
  denom_eq w y

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    0 < denom w y :=
  denom_pos w hy

example (y : Spacetime) :
    (y 0 - tau w y) ^ 2 = sep w y 0 ^ 2 + sep w y 1 ^ 2 + sep w y 2 ^ 2 :=
  sep_sq w y

example (u v : Space 3) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 :=
  inner_eq_sum u v

example (u : Space 3) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 :=
  norm_sq_eq_sum u

example {f : ℝ → Space 3} {s : ℝ} (hf : DifferentiableAt ℝ f s) (i : Fin 3) :
    HasDerivAt (fun s => f s i) (deriv f s i) s :=
  hasDerivAt_component hf i

example {f : ℝ → Space 3} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ fun s => f s i :=
  contDiff_component hf i

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (tau w) ((y 0 - tau w y) / denom w y) (-(denom w y)⁻¹ • sep w y) y :=
  hasGradAt_tau w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' (tau w y)) :
    HasGradAt (fun z => g (tau w z)) (g' * ((y 0 - tau w y) / denom w y))
      (g' • (-(denom w y)⁻¹ • sep w y)) y :=
  hasGradAt_comp_tau w hy hg

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    HasGradAt (fun z => sep w z i) (0 - vel w y i * ((y 0 - tau w y) / denom w y))
      (EuclideanSpace.single i 1 - vel w y i • (-(denom w y)⁻¹ • sep w y)) y :=
  hasGradAt_sep w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (fun z => z 0 - tau w z) (1 - (y 0 - tau w y) / denom w y)
      (0 - -(denom w y)⁻¹ • sep w y) y :=
  hasGradAt_dist w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    HasGradAt (fun z => vel w z i) (acc w y i * ((y 0 - tau w y) / denom w y))
      (acc w y i • (-(denom w y)⁻¹ • sep w y)) y :=
  hasGradAt_vel w hy i

example (y : Spacetime) :
    Spacetime →L[ℝ] ℝ :=
  tauDeriv w y

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasFDerivAt (sep w)
      ((space : Spacetime →L[ℝ] Space 3) - (tauDeriv w y).smulRight (vel w y)) y :=
  hasFDerivAt_sep w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasFDerivAt (vel w) ((tauDeriv w y).smulRight (acc w y)) y :=
  hasFDerivAt_vel w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (denom w) (1 - kfac w y * ((y 0 - tau w y) / denom w y))
      (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y)) y :=
  hasGradAt_denom w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (tau w) y :=
  contDiffAt_tau w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiffAt ℝ ∞ (fun z => g (tau w z)) y :=
  contDiffAt_comp_tau w hy hg

example (μ : Fin 4) (y : Spacetime) :
    ContDiffAt ℝ ∞ (fun z : Spacetime => z μ) y :=
  contDiffAt_coord μ y

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => sep w z i) y :=
  contDiffAt_sep w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => vel w z i) y :=
  contDiffAt_vel w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (fun z => z 0 - tau w z) y :=
  contDiffAt_dist w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (denom w) y :=
  contDiffAt_denom w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (fun z => (denom w z)⁻¹) y :=
  contDiffAt_inv_denom w hy

example :
    (2 : ℕ∞ω) ≤ ∞ :=
  two_le_infty

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    gradPairing (tau w) (tau w) y = 0 :=
  gradPairing_tau w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (tau w) y = -2 / denom w y :=
  box_tau w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s)
    (hg' : Differentiable ℝ g') :
    box (fun z => g (tau w z)) y = g' (tau w y) * (-2 / denom w y) :=
  box_comp_tau w hy hg hg'

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (fun z => sep w z i) y = -vel w y i * (-2 / denom w y) :=
  box_sep w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (fun z => vel w z i) y = acc w y i * (-2 / denom w y) :=
  box_vel w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (fun z => z 0 - tau w z) y = 2 / denom w y :=
  box_dist w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    gradPairing (fun z => sep w z i) (fun z => vel w z i) y =
      -(acc w y i * sep w y i) / denom w y :=
  gradPairing_sep_vel w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (denom w) y =
      (2 * (1 - ‖vel w y‖ ^ 2) + 4 * inner ℝ (sep w y) (acc w y)) / denom w y :=
  box_denom w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    gradPairing (denom w) (denom w) y = 1 - ‖vel w y‖ ^ 2 + 2 * inner ℝ (sep w y) (acc w y) :=
  gradPairing_denom w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (fun z => (denom w z)⁻¹) y = 0 :=
  box_inv_denom w hy

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    gradPairing (fun z => vel w z i) (fun z => (denom w z)⁻¹) y = acc w y i / denom w y ^ 2 :=
  gradPairing_vel_inv_denom w hy i

example {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (fun z => vel w z i * (denom w z)⁻¹) y = 0 :=
  box_vel_inv_denom w hy i

example (e : ℝ) (w : SubluminalWorldline) (y : Spacetime) :
    ℝ :=
  scalarPotential e w y

example (e : ℝ) (w : SubluminalWorldline) (y : Spacetime) :
    Fin 3 → ℝ :=
  vectorPotential e w y

example (e : ℝ) :
    scalarPotential e w = fun z => e / (4 * Real.pi) * (denom w z)⁻¹ :=
  scalarPotential_eq w e

example (e : ℝ) (i : Fin 3) :
    (fun z => vectorPotential e w z i) =
      fun z => e / (4 * Real.pi) * (vel w z i * (denom w z)⁻¹) :=
  vectorPotential_eq w e i

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    HasGradAt (scalarPotential e w)
      (e / (4 * Real.pi) * (-(denom w y ^ 2)⁻¹ * (1 - kfac w y * ((y 0 - tau w y) / denom w y))))
      ((e / (4 * Real.pi)) • (-(denom w y ^ 2)⁻¹ •
        (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y)))) y :=
  hasGradAt_scalarPotential w e hy

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    HasGradAt (fun z => vectorPotential e w z i)
      (e / (4 * Real.pi) * (vel w y i * (-(denom w y ^ 2)⁻¹ *
        (1 - kfac w y * ((y 0 - tau w y) / denom w y))) +
          (denom w y)⁻¹ * (acc w y i * ((y 0 - tau w y) / denom w y))))
      ((e / (4 * Real.pi)) • (vel w y i • (-(denom w y ^ 2)⁻¹ •
        (-vel w y - kfac w y • (-(denom w y)⁻¹ • sep w y))) +
          (denom w y)⁻¹ • (acc w y i • (-(denom w y)⁻¹ • sep w y)))) y :=
  hasGradAt_vectorPotential w e hy i

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (scalarPotential e w) y :=
  contDiffAt_scalarPotential w e hy

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => vectorPotential e w z i) y :=
  contDiffAt_vectorPotential w e hy i

end LienardWiechert

open LienardWiechert

example (e : ℝ) (w : SubluminalWorldline) :
    Potential :=
  lienardWiechert e w

variable (w : SubluminalWorldline)

example (e : ℝ) :
    potentialComponent (lienardWiechert e w) 0 = fun y => -scalarPotential e w y :=
  potentialComponent_lienardWiechert_zero w e

example (e : ℝ) (i : Fin 3) :
    potentialComponent (lienardWiechert e w) i.succ = fun y => vectorPotential e w y i :=
  potentialComponent_lienardWiechert_succ w e i

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    ContDiffAt ℝ ∞ (lienardWiechert e w) y :=
  contDiffAt_lienardWiechert w e hy

example (e : ℝ) :
    ContDiffOn ℝ ∞ (lienardWiechert e w) w.offWorldline :=
  contDiffOn_lienardWiechert w e

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    lorenzDivergence (lienardWiechert e w) y = 0 :=
  lorenzDivergence_lienardWiechert w e hy

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    box (potentialComponent (lienardWiechert e w) 0) y = 0 :=
  box_lienardWiechert_zero w e hy

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) (i : Fin 3) :
    box (potentialComponent (lienardWiechert e w) i.succ) y = 0 :=
  box_lienardWiechert_succ w e hy i

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    (divergence3 (magneticField (fieldTensor (lienardWiechert e w))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (lienardWiechert e w)) i) 0 y +
        curl (electricField (fieldTensor (lienardWiechert e w))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (lienardWiechert e w))) y = 0 ∧
    ∀ i, curl (magneticField (fieldTensor (lienardWiechert e w))) y i -
        partialAt (electricField (fieldTensor (lienardWiechert e w)) i) 0 y = 0 :=
  maxwell_lienardWiechert w e hy

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    exteriorDerivative (fun z => -star (fieldTensor (lienardWiechert e w) z)) y = 0 :=
  excitation_lienardWiechert w e hy

namespace LienardWiechert

example (e : ℝ) (w : SubluminalWorldline) (t : ℝ) (x : Space 3) :
    Space 3 :=
  velocityField e w t x

example (e : ℝ) (w : SubluminalWorldline) (t : ℝ) (x : Space 3) :
    Space 3 :=
  accelerationField e w t x

example {f : Spacetime → ℝ} {a : ℝ} {b : Space 3} {y : Spacetime} (hf : HasGradAt f a b y)
    {μ : Fin 4} (i : Fin 3) (h : μ = i.succ) :
    partialAt f μ y = b i :=
  HasGradAt.partialAt_succ' hf i h

end LienardWiechert

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    electricVector (fieldTensor (lienardWiechert e w) y) =
      WithLp.ofLp (velocityField e w (y 0) (space y) + accelerationField e w (y 0) (space y)) :=
  electricVector_lienardWiechert w e hy

example (e : ℝ) {y : Spacetime} (hy : y ∈ w.offWorldline) :
    magneticVector (fieldTensor (lienardWiechert e w) y) =
      crossProduct (WithLp.ofLp (w.retardedDirection (y 0) (space y)))
        (electricVector (fieldTensor (lienardWiechert e w) y)) :=
  magneticVector_lienardWiechert w e hy

namespace LienardWiechert

example (e : ℝ) (t : ℝ) (x : Space 3) :
    WithLp.ofLp (accelerationField e w t x) =
      (e / (4 * Real.pi * w.retardedDenominator t x ^ 3)) •
        crossProduct (WithLp.ofLp (w.retardedSeparation t x))
          (crossProduct (WithLp.ofLp (w.retardedSeparation t x -
              ‖w.retardedSeparation t x‖ • w.retardedVelocity t x))
            (WithLp.ofLp (w.retardedAcceleration t x))) :=
  accelerationField_eq_cross w e t x

example {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    Minkowski.vector (τ + ρ) (w.r τ + ρ • n) ∈ w.offWorldline :=
  mem_offWorldline_lightCone w hρ hn

example {τ ρ : ℝ} (hρ : 0 ≤ ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    w.retardedTime (τ + ρ) (w.r τ + ρ • n) = τ :=
  retardedTime_lightCone w hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    velocityField e w (τ + ρ) (w.r τ + ρ • n) =
      (e * (1 - ‖deriv w.r τ‖ ^ 2) /
        (4 * Real.pi * ρ ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) • (n - deriv w.r τ) :=
  velocityField_lightCone w e hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    accelerationField e w (τ + ρ) (w.r τ + ρ • n) =
      (e / (4 * Real.pi * ρ * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
        (inner ℝ n (deriv (deriv w.r) τ) • (n - deriv w.r τ) -
          inner ℝ n (n - deriv w.r τ) • deriv (deriv w.r) τ) :=
  accelerationField_lightCone w e hρ hn

end LienardWiechert

namespace LienardWiechert

example (r₀ v : Space 3) (hv : ‖v‖ < 1) (s : ℝ) :
    deriv (deriv (SubluminalWorldline.uniform r₀ v hv).r) s = 0 :=
  deriv_deriv_uniform r₀ v hv s

example (e : ℝ) (r₀ v : Space 3) (hv : ‖v‖ < 1) (t : ℝ) (x : Space 3) :
    accelerationField e (SubluminalWorldline.uniform r₀ v hv) t x = 0 :=
  accelerationField_uniform e r₀ v hv t x

example (e : ℝ) (r₀ : Space 3) (t : ℝ) (x : Space 3) :
    velocityField e (SubluminalWorldline.rest r₀) t x =
      Electrostatics.pointChargeField e (x - r₀) :=
  velocityField_rest e r₀ t x

end LienardWiechert

example (e : ℝ) (r₀ : Space 3) {y : Spacetime}
    (hy : y ∈ (SubluminalWorldline.rest r₀).offWorldline) :
    electricVector (fieldTensor (lienardWiechert e
        (SubluminalWorldline.rest r₀)) y) =
      WithLp.ofLp (Electrostatics.pointChargeField e (space y - r₀)) :=
  electricVector_lienardWiechert_rest e r₀ hy

example (V : ℝ) (hV : |V| < 1) :
    SubluminalWorldline :=
  axisWorldline V hV

example (V : ℝ) (hV : |V| < 1) {y : Spacetime} (hy : y ∈ (axisWorldline V hV).offWorldline) :
    ‖MovingCharge.comovingPosition V hV y‖ =
      (axisVelocity V hV).gamma * (axisWorldline V hV).retardedDenominator (y 0) (space y) :=
  norm_comovingPosition_axisWorldline V hV hy

example (e V : ℝ) (hV : |V| < 1) :
    lienardWiechert e (axisWorldline V hV) = MovingCharge.movingCoulomb V hV e :=
  lienardWiechert_axisWorldline e V hV

example (e V : ℝ) (hV : |V| < 1) :
    lienardWiechert e (axisWorldline V hV) =
      MovingCharge.movingScalar V hV (Electrostatics.pointChargePotential e) :=
  lienardWiechert_axisWorldline_eq_movingScalar e V hV

example (e τ : ℝ) (y : Space 3) :
    scalarPotential e w (Minkowski.vector (τ + ‖y‖) (w.r τ + y)) =
      e / (4 * Real.pi * (‖y‖ - inner ℝ y (deriv w.r τ))) :=
  scalarPotential_add_norm w e τ y

example (e τ : ℝ) (y : Space 3) (i : Fin 3) :
    vectorPotential e w (Minkowski.vector (τ + ‖y‖) (w.r τ + y)) i =
      e * deriv w.r τ i / (4 * Real.pi * (‖y‖ - inner ℝ y (deriv w.r τ))) :=
  vectorPotential_add_norm w e τ y i

example {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    w.retardedDirection (τ + ρ) (w.r τ + ρ • n) = n :=
  retardedDirection_lightCone w hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    electricVector (fieldTensor (lienardWiechert e w) (Minkowski.vector (τ + ρ) (w.r τ + ρ • n))) =
      WithLp.ofLp ((e * (1 - ‖deriv w.r τ‖ ^ 2) /
          (4 * Real.pi * ρ ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) • (n - deriv w.r τ) +
        (e / (4 * Real.pi * ρ * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
          (inner ℝ n (deriv (deriv w.r) τ) • (n - deriv w.r τ) -
            inner ℝ n (n - deriv w.r τ) • deriv (deriv w.r) τ)) :=
  electricVector_lienardWiechert_lightCone w e hρ hn

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3} (hn : ‖n‖ = 1) :
    magneticVector (fieldTensor (lienardWiechert e w) (Minkowski.vector (τ + ρ) (w.r τ + ρ • n))) =
      crossProduct (WithLp.ofLp n) (electricVector (fieldTensor (lienardWiechert e w)
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)))) :=
  magneticVector_lienardWiechert_lightCone w e hρ hn

end ProjectAinos.Electrodynamics

end LienardWiechert

section LienardWiechertSource

open MeasureTheory Filter Set Metric

open scoped Topology ContDiff ENNReal

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SpecialRelativity

open SmoothGeometry.Minkowski (Space)

example :
    MeasurePreserving (Wave.timeSpaceEquiv : Spacetime → ℝ × Space 3) :=
  measurePreserving_timeSpaceEquiv

example :
    Spacetime ≃ᵐ ℝ × Space 3 :=
  timeSpaceMeasurableEquiv

example :
    (timeSpaceMeasurableEquiv : Spacetime → ℝ × Space 3) = Wave.timeSpaceEquiv :=
  coe_timeSpaceMeasurableEquiv

example (p : ℝ × Space 3) :
    timeSpaceMeasurableEquiv.symm p = Minkowski.vector p.1 p.2 :=
  timeSpaceMeasurableEquiv_symm_apply p

example :
    MeasurePreserving (timeSpaceMeasurableEquiv.symm : ℝ × Space 3 → Spacetime) :=
  measurePreserving_timeSpaceMeasurableEquiv_symm

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Spacetime → F) :
    ∫ v, g v = ∫ p : ℝ × Space 3, g (Minkowski.vector p.1 p.2) :=
  integral_spacetime_eq g

example :
    ∀ᵐ q : ℝ × Space 3, q.2 ≠ 0 :=
  ae_snd_ne_zero

example :
    MeasurableSet {q : ℝ × Space 3 | q.2 ≠ 0} :=
  measurableSet_snd_ne_zero

example :
    (volume : Measure (ℝ × Space 3)).restrict {q | q.2 ≠ 0} = volume :=
  restrict_snd_ne_zero

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

example :
    IsClosed {p : ℝ × Space 3 | p.2 = w.r p.1} :=
  isClosed_worldline w

example :
    volume {p : ℝ × Space 3 | p.2 = w.r p.1} = 0 :=
  volume_worldline w

example :
    ∀ᵐ p : ℝ × Space 3, p.2 ≠ w.r p.1 :=
  ae_offWorldline w

example (q : ℝ × Space 3) :
    w.lightConeEquiv q = (q.1 + ‖q.2‖, w.r q.1 + q.2) :=
  lightConeEquiv_apply w q

example (p : ℝ × Space 3) :
    w.lightConeEquiv.symm p = (w.retardedTime p.1 p.2, w.retardedSeparation p.1 p.2) :=
  lightConeEquiv_symm_apply w p

example :
    Continuous w.lightConeEquiv :=
  continuous_lightConeEquiv w

example (q : ℝ × Space 3) :
    ℝ × Space 3 →L[ℝ] ℝ × Space 3 :=
  lightConeDeriv w q

example {q : ℝ × Space 3} (hq : q.2 ≠ 0) :
    HasFDerivAt w.lightConeEquiv (w.lightConeDeriv q) q :=
  hasFDerivAt_lightConeEquiv w hq

example (q : ℝ × Space 3) :
    ℝ :=
  lightConeJacobian w q

example (q : ℝ × Space 3) :
    (w.lightConeDeriv q).det = w.lightConeJacobian q :=
  det_lightConeDeriv w q

example :
    w.lightConeEquiv '' {q | q.2 ≠ 0} = {p | p.2 ≠ w.r p.1} :=
  image_lightConeEquiv w

example (q : ℝ × Space 3) :
    1 - w.v₀ ≤ w.lightConeJacobian q :=
  sub_le_lightConeJacobian w q

example (q : ℝ × Space 3) :
    0 < w.lightConeJacobian q :=
  lightConeJacobian_pos w q

example (q : ℝ × Space 3) :
    |(w.lightConeDeriv q).det| = w.lightConeJacobian q :=
  abs_det_lightConeDeriv w q

example :
    (volume : Measure (ℝ × Space 3)).restrict (w.lightConeEquiv '' {q | q.2 ≠ 0}) = volume :=
  restrict_image_lightConeEquiv w

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ × Space 3 → F) :
    ∫ p, g p = ∫ q, w.lightConeJacobian q • g (w.lightConeEquiv q) :=
  integral_lightCone w g

example (g : ℝ × Space 3 → ℝ≥0∞) :
    ∫⁻ p, g p = ∫⁻ q, ENNReal.ofReal (w.lightConeJacobian q) * g (w.lightConeEquiv q) :=
  lintegral_lightCone w g

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ × Space 3 → F) :
    Integrable g ↔ Integrable fun q => w.lightConeJacobian q • g (w.lightConeEquiv q) :=
  integrable_lightCone_iff w g

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ × Space 3 → F)
    {s : Set (ℝ × Space 3)} (hs : MeasurableSet s) :
    IntegrableOn g s ↔ IntegrableOn (fun q => w.lightConeJacobian q • g (w.lightConeEquiv q))
      (w.lightConeEquiv ⁻¹' s) :=
  integrableOn_lightCone_iff w g hs

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ × Space 3 → F}
    (hg : Integrable g) :
    ∫ p, g p = ∫ τ, ∫ y : Space 3,
      (1 - inner ℝ y (deriv w.r τ) / ‖y‖) • g (τ + ‖y‖, w.r τ + y) :=
  integral_lightCone_iterated w hg

example (T ρ : ℝ) :
    w.lightConeEquiv ⁻¹' {p | |p.1| ≤ T ∧ ‖p.2‖ ≤ ρ} ⊆
      Icc (-((T + ρ + ‖w.r 0‖) / (1 - w.v₀))) ((T + ρ + ‖w.r 0‖) / (1 - w.v₀)) ×ˢ
        closedBall 0 (T + (T + ρ + ‖w.r 0‖) / (1 - w.v₀)) :=
  lightConeEquiv_preimage_subset w T ρ

example {K : Set (ℝ × Space 3)} (hK : Bornology.IsBounded K) :
    ∃ M L : ℝ, w.lightConeEquiv ⁻¹' K ⊆ Icc (-M) M ×ˢ closedBall 0 L :=
  exists_lightConeEquiv_preimage_subset w hK

end SubluminalWorldline

example {c : ℝ → ℝ} (hc : Continuous c) (M L : ℝ) :
    IntegrableOn (fun q : ℝ × Space 3 => c q.1 * SmoothGeometry.Potential.newtonKernel q.2)
      (Icc (-M) M ×ˢ closedBall 0 L) :=
  integrableOn_mul_newtonKernel hc M L

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

example {q : ℝ × Space 3} (hq : q.2 ≠ 0) :
    0 < ‖q.2‖ - inner ℝ q.2 (deriv w.r q.1) :=
  norm_sub_inner_pos w hq

example (e : ℝ) {q : ℝ × Space 3} (hq : q.2 ≠ 0) :
    w.lightConeJacobian q *
        LienardWiechert.scalarPotential e w (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) =
      e / (4 * Real.pi * ‖q.2‖) :=
  lightConeJacobian_mul_scalarPotential w e hq

example (e : ℝ) {q : ℝ × Space 3} (hq : q.2 ≠ 0) (i : Fin 3) :
    w.lightConeJacobian q *
        LienardWiechert.vectorPotential e w (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) i =
      e * deriv w.r q.1 i / (4 * Real.pi * ‖q.2‖) :=
  lightConeJacobian_mul_vectorPotential w e hq i

example (e : ℝ) (g : Spacetime → ℝ) :
    ∫ v, LienardWiechert.scalarPotential e w v * g v =
      ∫ q : ℝ × Space 3, e / (4 * Real.pi * ‖q.2‖) *
        g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) :=
  integral_scalarPotential_mul w e g

example (e : ℝ) (i : Fin 3) (g : Spacetime → ℝ) :
    ∫ v, LienardWiechert.vectorPotential e w v i * g v =
      ∫ q : ℝ × Space 3, e * deriv w.r q.1 i / (4 * Real.pi * ‖q.2‖) *
        g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) :=
  integral_vectorPotential_mul w e i g

example {g : Spacetime → ℝ} {c : ℝ → ℝ} (hc : Continuous c)
    (hg : ∀ q : ℝ × Space 3, q.2 ≠ 0 →
      w.lightConeJacobian q * g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) =
        c q.1 / (4 * Real.pi * ‖q.2‖)) :
    LocallyIntegrable g :=
  locallyIntegrable_of_lightCone w hc hg

example (e : ℝ) :
    LocallyIntegrable (LienardWiechert.scalarPotential e w) :=
  locallyIntegrable_scalarPotential w e

example (e : ℝ) (i : Fin 3) :
    LocallyIntegrable fun v => LienardWiechert.vectorPotential e w v i :=
  locallyIntegrable_vectorPotential w e i

example (e : ℝ) (μ : Fin 4) :
    LocallyIntegrable (potentialComponent (lienardWiechert e w) μ) :=
  locallyIntegrable_potentialComponent w e μ

end SubluminalWorldline

example (u : ℝ × Space 3 → ℝ) (p : ℝ × Space 3) :
    Wave.waveOperator (fun p => u (-p)) p = Wave.waveOperator u (-p) :=
  waveOperator_comp_neg u p

example {u : ℝ × Space 3 → ℝ} (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u) (τ : ℝ)
    (x : Space 3) :
    ∫ y : Space 3, Wave.waveOperator u (τ + ‖y‖, x + y) / (4 * Real.pi * ‖y‖) = u (τ, x) :=
  integral_wave_div_norm_advanced hu hc τ x

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

example {c : ℝ → ℝ} (hc : Continuous c) {u : ℝ × Space 3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) :
    ∫ q : ℝ × Space 3, c q.1 * SmoothGeometry.Potential.newtonKernel q.2 *
        Wave.waveOperator u (w.lightConeEquiv q) =
      ∫ τ, c τ * u (τ, w.r τ) :=
  integral_mul_newtonKernel_mul_wave w hc hu hcs

end SubluminalWorldline

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) :
    box χ = fun v => -Wave.waveOperator (fun p => χ (Wave.timeSpaceEquiv.symm p))
      (Wave.timeSpaceEquiv v) :=
  box_eq_neg_waveOperator hχ

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) :
    Continuous (box χ) :=
  continuous_box hχ

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    HasCompactSupport (box χ) :=
  hasCompactSupport_box hχ hc

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

example {g : Spacetime → ℝ} {c : ℝ → ℝ} (hc : Continuous c)
    (hg : ∀ q : ℝ × Space 3, q.2 ≠ 0 →
      w.lightConeJacobian q * g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) =
        c q.1 / (4 * Real.pi * ‖q.2‖))
    {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    ∫ v, g v * box χ v = -∫ t, c t * χ (Minkowski.vector t (w.r t)) :=
  integral_mul_box_of_lightCone w hc hg hχ hχc

example (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    ∫ v, LienardWiechert.scalarPotential e w v * box χ v =
      -(e * ∫ t, χ (Minkowski.vector t (w.r t))) :=
  integral_scalarPotential_mul_box w e hχ hc

example (e : ℝ) (i : Fin 3) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    ∫ v, LienardWiechert.vectorPotential e w v i * box χ v =
      -(e * ∫ t, deriv w.r t i * χ (Minkowski.vector t (w.r t))) :=
  integral_vectorPotential_mul_box w e i hχ hc

example (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    ∫ v, potentialComponent (lienardWiechert e w) 0 v * box χ v =
        e * ∫ t, χ (Minkowski.vector t (w.r t)) ∧
      ∀ i : Fin 3, ∫ v, potentialComponent (lienardWiechert e w) i.succ v * box χ v =
        -(e * ∫ t, deriv w.r t i * χ (Minkowski.vector t (w.r t))) :=
  integral_potentialComponent_mul_box w e hχ hc

example (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    Integrable fun v => LienardWiechert.scalarPotential e w v * box χ v :=
  integrable_scalarPotential_mul_box w e hχ hc

example (e : ℝ) (i : Fin 3) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    Integrable fun v => LienardWiechert.vectorPotential e w v i * box χ v :=
  integrable_vectorPotential_mul_box w e i hχ hc

example (h : ‖w.r 0‖ < 2) :
    0 < ∫ t, spacetimeBump (Minkowski.vector t (w.r t)) :=
  integral_spacetimeBump_pos w h

example {e : ℝ} (he : e ≠ 0) (h : ‖w.r 0‖ < 2) :
    ∫ v, LienardWiechert.scalarPotential e w v * box spacetimeBump v ≠ 0 :=
  integral_scalarPotential_mul_box_spacetimeBump_ne_zero w he h

example (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    ∫ v, LienardWiechert.scalarPotential e (rest 0) v * box χ v =
      -(e * ∫ t, χ (Minkowski.vector t 0)) :=
  integral_scalarPotential_mul_box_rest e hχ hc

example {e : ℝ} (he : e ≠ 0) :
    ∫ v, LienardWiechert.scalarPotential e (rest 0) v * box spacetimeBump v ≠ 0 :=
  integral_scalarPotential_mul_box_rest_ne_zero he

example {e ρ Ω : ℝ} (he : e ≠ 0) (h : |ρ * Ω| < 1) (hρ : |ρ| < 2) :
    ∫ v, LienardWiechert.scalarPotential e (circular ρ Ω h) v * box spacetimeBump v ≠ 0 :=
  integral_scalarPotential_mul_box_circular_ne_zero he h hρ

end SubluminalWorldline

end ProjectAinos.Electrodynamics

end LienardWiechertSource

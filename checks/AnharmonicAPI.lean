/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.OneDimension.Anharmonic
import ProjectAInos.Mechanics.Oscillations.AnharmonicNormalForm

/-! Typed contracts for the anharmonic oscillator: the implicit function
theorem for one real equation, the period of the oscillation in the potential
`ν²x²/2 + αx³/3 + βx⁴/4` as a function of the squared half-width and the shift
of the frequency, and the Birkhoff normal form of the formal Hamiltonian with
its coefficient of degree four. These examples use default elaborator
options. -/

open ProjectAInos ProjectAInos.SmoothAlgebra ProjectAInos.Mechanics
open ProjectAInos.SmoothAlgebra.FormalSeries
open Set Filter MeasureTheory MvPowerSeries
open scoped Real ContDiff Topology

noncomputable section

example {Φ Φ' : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hd : ∀ v : ℝ × ℝ, HasDerivAt (fun y => Φ (v.1, y)) (Φ' v) v.2) (hc : Continuous Φ')
    {u : ℝ × ℝ} (hu : Φ' u ≠ 0) :
    ∃ (J : Set ℝ) (ψ : ℝ → ℝ), IsOpen J ∧ u.1 ∈ J ∧ ψ u.1 = u.2 ∧ ContDiffOn ℝ ∞ ψ J ∧
      ∀ s ∈ J, Φ' (s, ψ s) ≠ 0 ∧ Φ (s, ψ s) = Φ u :=
  exists_contDiffOn_implicitFunction_real hΦ hd hc hu

section Anharmonic

open OneDim OneDim.Anharmonic

variable {ν α β : ℝ}

example (ν α β x : ℝ) :
    potential ν α β x =
      ν ^ 2 * x ^ 2 / 2 + α * x ^ 3 / 3 + β * x ^ 4 / 4 := rfl

example (ν α β p q : ℝ) :
    firstDifference ν α β p q =
      ν ^ 2 * (p + q) / 2 + α * (p ^ 2 + p * q + q ^ 2) / 3 +
      β * (p ^ 3 + p ^ 2 * q + p * q ^ 2 + q ^ 3) / 4 := rfl

example (ν α β a b x : ℝ) :
    factor ν α β a b x =
      ν ^ 2 / 2 + α / 3 * (a + b + x) +
        β / 4 * (a ^ 2 + b ^ 2 + x ^ 2 + a * b + a * x + b * x) := rfl

example (ν α β : ℝ) :
    ContDiff ℝ ∞ (potential ν α β) :=
  contDiff_potential ν α β

example (ν α β x : ℝ) :
    HasDerivAt (potential ν α β) (ν ^ 2 * x + α * x ^ 2 + β * x ^ 3) x :=
  hasDerivAt_potential ν α β x

example (ν α β x : ℝ) :
    deriv (potential ν α β) x = ν ^ 2 * x + α * x ^ 2 + β * x ^ 3 :=
  deriv_potential ν α β x

example (ν α β p q : ℝ) :
    potential ν α β p - potential ν α β q = (p - q) * firstDifference ν α β p q :=
  potential_sub ν α β p q

example (ν α β p q : ℝ) :
    dividedDifference (potential ν α β) (p, q) = firstDifference ν α β p q :=
  dividedDifference_potential ν α β p q

example (ν α β a b : ℝ) :
    wellFactor (potential ν α β) a b = factor ν α β a b :=
  wellFactor_potential ν α β a b

example (ν α β : ℝ) (v : ℝ × ℝ) :
    slopeEquation ν α β v =
      v.2 * (ν ^ 2 + α * v.1 * v.2 + β * v.1 ^ 2 * v.2 ^ 2 + β * v.1) + α / 3 := rfl

example (ν α β ρ e : ℝ) (h : slopeEquation ν α β (ρ ^ 2, e) = 0) :
    potential ν α β (ρ ^ 2 * e - ρ) = potential ν α β (ρ ^ 2 * e + ρ) :=
  potential_centre ν α β ρ e h

example (hν : 0 < ν) (α β : ℝ) :
    ∃ (J : Set ℝ) (e : ℝ → ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ e 0 = -α / (3 * ν ^ 2) ∧
      ContDiffOn ℝ ∞ e J ∧ ∀ s ∈ J, slopeEquation ν α β (s, e s) = 0 :=
  exists_slope hν α β

example (hν : 0 < ν) (α β : ℝ) {J : Set ℝ} {e : ℝ → ℝ} (hJ : IsOpen J)
    (h0 : (0 : ℝ) ∈ J) (he : ContDiffOn ℝ ∞ e J)
    (hsol : ∀ s ∈ J, slopeEquation ν α β (s, e s) = 0) :
    ∃ ρ₀ > 0, ∀ ρ ∈ Ioo 0 ρ₀, ρ ^ 2 ∈ J ∧
      IsWell (potential ν α β) (potential ν α β (ρ ^ 2 * e (ρ ^ 2) + ρ))
        (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) :=
  exists_isWell hν α β hJ h0 he hsol

example (P R : ℝ) :
    symRoot P R =
      √(2 * P + 2 * √(P ^ 2 - R)) / √(P ^ 2 - R) := rfl

example {P r : ℝ} (h1 : 0 < P - r) (h2 : 0 < P + r) :
    1 / √(P - r) + 1 / √(P + r) = symRoot P (r ^ 2) :=
  inv_sqrt_add_inv_sqrt h1 h2

example (hν : 0 < ν) {P R : ℝ → ℝ} {p₁ r₁ s₀ : ℝ}
    (hP : HasDerivAt P p₁ s₀) (hR : HasDerivAt R r₁ s₀) (hP0 : P s₀ = ν ^ 2) (hR0 : R s₀ = 0) :
    HasDerivAt (fun s => symRoot (P s) (R s)) (-p₁ / ν ^ 3 + 3 * r₁ / (4 * ν ^ 5)) s₀ :=
  hasDerivAt_symRoot hν hP hR hP0 hR0

example (ν α β : ℝ) (e : ℝ → ℝ) (s θ : ℝ) :
    kernelP ν α β e s θ =
      ν ^ 2 + 2 * α * (s * e s) + 3 * β * (s * e s) ^ 2 + β / 2 * s * (1 + Real.cos θ ^ 2) := rfl

example (α β : ℝ) (e : ℝ → ℝ) (s : ℝ) :
    kernelB α β e s =
      2 * α / 3 + 2 * β * (s * e s) := rfl

example (ν α β : ℝ) (e : ℝ → ℝ) (p : ℝ × ℝ) :
    kernel ν α β e p =
      symRoot (kernelP ν α β e p.1 p.2) (p.1 * kernelB α β e p.1 ^ 2 * Real.cos p.2 ^ 2) := rfl

example (ν α β : ℝ) (e : ℝ → ℝ) (s : ℝ) :
    periodFunction ν α β e s =
      (∫ θ in (0 : ℝ)..2 * π, kernel ν α β e (s, θ)) / 2 := rfl

example (ν α β : ℝ) (e : ℝ → ℝ) (ρ θ : ℝ) :
    2 * factor ν α β (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ)
        (orbitPosition (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) θ) =
      kernelP ν α β e (ρ ^ 2) θ - ρ * kernelB α β e (ρ ^ 2) * Real.cos θ :=
  two_mul_factor ν α β e ρ θ

example {a b : ℝ} (θ : ℝ)
    (hpos : 0 < factor ν α β a b (orbitPosition a b θ)) :
    orbitRate 1 (potential ν α β) a b θ =
      1 / √(2 * factor ν α β a b (orbitPosition a b θ)) :=
  orbitRate_eq θ hpos

example (ν α β : ℝ) (e : ℝ → ℝ) {ρ E : ℝ}
    (h : IsWell (potential ν α β) E (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ)) :
    orbitPeriod 1 (potential ν α β) (ρ ^ 2 * e (ρ ^ 2) - ρ) (ρ ^ 2 * e (ρ ^ 2) + ρ) =
      periodFunction ν α β e (ρ ^ 2) :=
  orbitPeriod_eq_periodFunction ν α β e h

example (hν : 0 < ν) (α β : ℝ) (e : ℝ → ℝ) (θ : ℝ) :
    kernel ν α β e (0, θ) = 2 / ν :=
  kernel_zero hν α β e θ

example (hν : 0 < ν) (α β : ℝ) (e : ℝ → ℝ) :
    periodFunction ν α β e 0 = 2 * π / ν :=
  periodFunction_zero hν α β e

example (ν α β θ : ℝ) :
    kernelDeriv ν α β θ =
      -(2 * α * (-α / (3 * ν ^ 2)) + β / 2 * (1 + Real.cos θ ^ 2)) / ν ^ 3 +
      3 * ((2 * α / 3) ^ 2 * Real.cos θ ^ 2) / (4 * ν ^ 5) := rfl

example (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ} {e' : ℝ}
    (he : HasDerivAt e e' 0) (he0 : e 0 = -α / (3 * ν ^ 2)) (θ : ℝ) :
    HasDerivAt (fun s => kernel ν α β e (s, θ)) (kernelDeriv ν α β θ) 0 :=
  hasDerivAt_kernel hν α β he he0 θ

example {P R : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hP : ContDiffAt ℝ 1 P x)
    (hR : ContDiffAt ℝ 1 R x) (h1 : 0 < P x) (h2 : R x < P x ^ 2) :
    ContDiffAt ℝ 1 (fun p => symRoot (P p) (R p)) x :=
  contDiffAt_symRoot hP hR h1 h2

example (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ} (he : ContDiffAt ℝ 1 e 0)
    (θ : ℝ) :
    ContDiffAt ℝ 1 (kernel ν α β e) (0, θ) :=
  contDiffAt_kernel hν α β he θ

example (hν : 0 < ν) (α β : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, kernelDeriv ν α β θ =
      5 * π * α ^ 2 / (3 * ν ^ 5) - 3 * π * β / (2 * ν ^ 3) :=
  integral_kernelDeriv hν α β

example (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ}
    (he : ContDiffAt ℝ 1 e 0) (he0 : e 0 = -α / (3 * ν ^ 2)) :
    HasDerivAt (periodFunction ν α β e)
      (5 * π * α ^ 2 / (6 * ν ^ 5) - 3 * π * β / (4 * ν ^ 3)) 0 :=
  hasDerivAt_periodFunction hν α β he he0

example (hν : 0 < ν) (α β : ℝ) {e : ℝ → ℝ}
    (he : ContDiffAt ℝ 1 e 0) (he0 : e 0 = -α / (3 * ν ^ 2)) :
    HasDerivAt (fun s => 2 * π / periodFunction ν α β e s)
      (3 * β / (8 * ν) - 5 * α ^ 2 / (12 * ν ^ 3)) 0 :=
  hasDerivAt_frequency hν α β he he0

example (hν : 0 < ν) (α β : ℝ) :
    ∃ (c : ℝ → ℝ) (ρ₀ : ℝ), 0 < ρ₀ ∧
      (∀ ρ ∈ Ioo 0 ρ₀,
        IsWell (potential ν α β) (potential ν α β (c ρ + ρ)) (c ρ - ρ) (c ρ + ρ)) ∧
      Tendsto (fun ρ => c ρ / ρ ^ 2) (𝓝[>] 0) (𝓝 (-α / (3 * ν ^ 2))) ∧
      Tendsto
        (fun ρ => (2 * π / orbitPeriod 1 (potential ν α β) (c ρ - ρ) (c ρ + ρ) - ν) / ρ ^ 2)
        (𝓝[>] 0) (𝓝 (3 * β / (8 * ν) - 5 * α ^ 2 / (12 * ν ^ 3))) :=
  exists_tendsto_frequency hν α β

end Anharmonic

section NormalForm

open AnharmonicNormalForm

local notation "q" => (X 0 : PhaseSeries)
local notation "p" => (X 1 : PhaseSeries)

variable {ν : ℝ}

example :
    cubic =
      3 • (q ^ 2 * p) + 2 • p ^ 3 := rfl

example :
    quarticA =
      5 • (q ^ 3 * p) + 3 • (q * p ^ 3) := rfl

example :
    quarticB =
      q * p ^ 3 - q ^ 3 * p := rfl

example :
    bracket action cubic = 3 • q ^ 3 :=
  bracket_action_cubic

example :
    bracket cubic (q ^ 3) = -(9 • q ^ 4 + 18 • (q ^ 2 * p ^ 2)) :=
  bracket_cubic_pow

example :
    bracket action quarticA = 8 • q ^ 4 - 3 • (q ^ 2 + p ^ 2) ^ 2 :=
  bracket_action_quarticA

example :
    bracket action quarticB = 8 • (q ^ 2 * p ^ 2) - (q ^ 2 + p ^ 2) ^ 2 :=
  bracket_action_quarticB

example :
    action ^ 2 = (4⁻¹ : ℝ) • (q ^ 2 + p ^ 2) ^ 2 :=
  action_sq

example (i : Fin 2) (n : ℕ) :
    (X i : PhaseSeries) ^ n ∈ homogeneous n :=
  X_pow_mem_homogeneous i n

example :
    cubic ∈ homogeneous 3 :=
  cubic_mem

example :
    quarticA ∈ homogeneous 4 :=
  quarticA_mem

example :
    quarticB ∈ homogeneous 4 :=
  quarticB_mem

example (ν a b : ℝ) :
    hamiltonian ν a b =
      ν • action + a • q ^ 3 + b • q ^ 4 := rfl

example (ν a : ℝ) :
    generator₃ ν a =
      (a / (3 * ν)) • cubic := rfl

example (ν a b : ℝ) :
    quarticPart ν a b =
      (b - 3 * a ^ 2 / (2 * ν)) • q ^ 4 + (-(3 * a ^ 2 / ν)) • (q ^ 2 * p ^ 2) := rfl

example (ν a b : ℝ) :
    quarticGenerator ν a b =
      ((b - 3 * a ^ 2 / (2 * ν)) / 8) • quarticA + (-(3 * a ^ 2 / ν) / 8) • quarticB := rfl

example (ν a b : ℝ) :
    generator₄ ν a b =
      ν⁻¹ • quarticGenerator ν a b := rfl

example (ν a b : ℝ) :
    secondCoefficient ν a b =
      3 * b / 2 - 15 * a ^ 2 / (4 * ν) := rfl

example (ν a : ℝ) :
    generator₃ ν a ∈ orderGE (Fin 2) 3 :=
  generator₃_mem ν a

example (ν a b : ℝ) :
    generator₄ ν a b ∈ orderGE (Fin 2) 4 :=
  generator₄_mem ν a b

example (ν a b : ℝ) :
    quarticPart ν a b ∈ orderGE (Fin 2) 4 :=
  quarticPart_mem ν a b

example (hν : ν ≠ 0) (a : ℝ) :
    bracket (generator₃ ν a) (ν • action) = -(a • q ^ 3) :=
  bracket_generator₃_action hν a

example (ν a b : ℝ) :
    quarticPart ν a b = b • q ^ 4 + (a / 2) • bracket (generator₃ ν a) (q ^ 3) :=
  smul_bracket_generator₃_pow ν a b

example (ν a b : ℝ) :
    quarticPart ν a b =
      bracket action (quarticGenerator ν a b) + secondCoefficient ν a b • action ^ 2 :=
  quarticPart_eq ν a b

example (hν : ν ≠ 0) (a b : ℝ) :
    bracket (generator₄ ν a b) (ν • action) =
      -(quarticPart ν a b - secondCoefficient ν a b • action ^ 2) :=
  bracket_generator₄_action hν a b

example (ν a b : ℝ) :
    hamiltonian ν a b ∈ orderGE (Fin 2) 2 :=
  hamiltonian_mem ν a b

example (hν : ν ≠ 0) (a b : ℝ) :
    lieExp (ad (generator₃ ν a)) (hamiltonian ν a b) - (ν • action + quarticPart ν a b) ∈
      orderGE (Fin 2) 5 :=
  lieExp_generator₃ hν a b

example (hν : ν ≠ 0) (a b : ℝ) :
    lieExp (ad (generator₄ ν a b)) (lieExp (ad (generator₃ ν a)) (hamiltonian ν a b)) -
        (ν • action + secondCoefficient ν a b • action ^ 2) ∈ orderGE (Fin 2) 5 :=
  lieExp_generator₄ hν a b

example {k : ℕ} :
    homogeneousComponent k (action ^ 2) = if k = 4 then action ^ 2 else 0 :=
  homogeneousComponent_action_sq

example (hν : ν ≠ 0) (a b : ℝ) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ (hamiltonian ν a b) = PowerSeries.subst action h ∧ PowerSeries.coeff 0 h = 0 ∧
          PowerSeries.coeff 1 h = ν ∧ PowerSeries.coeff 2 h = secondCoefficient ν a b :=
  exists_normal_form hν a b

example (ν α β : ℝ) :
    physicalHamiltonian ν α β =
      (2⁻¹ : ℝ) • p ^ 2 + (ν ^ 2 / 2) • q ^ 2 + (α / 3) • q ^ 3 + (β / 4) • q ^ 4 := rfl

example {s : ℝ} (hs : s ≠ 0) (α β : ℝ) :
    scale s⁻¹ (inv_ne_zero hs) (physicalHamiltonian (s ^ 2) α β) =
      hamiltonian (s ^ 2) (α / (3 * s ^ 3)) (β / (4 * s ^ 4)) :=
  scale_physicalHamiltonian hs α β

example (hν : 0 < ν) (α β : ℝ) :
    ∃ (Ψ : PhaseSeries ≃ₐ[ℝ] PhaseSeries) (h : PowerSeries ℝ),
      (∀ f g, Ψ (bracket f g) = bracket (Ψ f) (Ψ g)) ∧
        Ψ (physicalHamiltonian ν α β) = PowerSeries.subst action h ∧
          PowerSeries.coeff 0 h = 0 ∧ PowerSeries.coeff 1 h = ν ∧
            PowerSeries.coeff 2 h = 3 * β / (8 * ν ^ 2) - 5 * α ^ 2 / (12 * ν ^ 4) :=
  exists_normal_form_physical hν α β

example (hν : ν ≠ 0) (α β ρ : ℝ) :
    2 * (3 * β / (8 * ν ^ 2) - 5 * α ^ 2 / (12 * ν ^ 4)) * (ν * ρ ^ 2 / 2) =
      (3 * β / (8 * ν) - 5 * α ^ 2 / (12 * ν ^ 3)) * ρ ^ 2 :=
  two_mul_coefficient_mul_action hν α β ρ

end NormalForm

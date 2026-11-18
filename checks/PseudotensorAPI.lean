/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.Pseudotensor

/-! Public consumers of the energy-momentum pseudotensor: the identities of the superpotential
for arrays, the product rule at a critical point, the superpotential with its antisymmetry and
the conservation identity, the second derivatives of the coefficients, the inverse, the density
and the Christoffel symbols at a point where the first derivatives vanish, the identity
`∂_l h^{ikl} = 2 |g| G^{ik}` there, and the pseudotensor with its vanishing, its symmetry and the
conservation of the total energy and momentum. Default elaborator options are intentional: these
checks must not rely on the implementation's transparency settings. Every statement is pinned
with its type. -/

noncomputable section

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

section Critical

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

example {u v : F → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hu0 : fderiv ℝ u x = 0) (hv0 : fderiv ℝ v x = 0) (a b : F) :
    fderiv ℝ (fun w => fderiv ℝ (fun y => u y * v y) w b) x a =
      fderiv ℝ (fun w => fderiv ℝ u w b) x a * v x +
        u x * fderiv ℝ (fun w => fderiv ℝ v w b) x a :=
  fderiv_fderiv_mul_of_critical hu hv hu0 hv0 a b

example {u v : F → ℝ} {x : F} (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hu0 : fderiv ℝ u x = 0) (hv0 : fderiv ℝ v x = 0) :
    fderiv ℝ (fun y => u y * v y) x = 0 :=
  fderiv_mul_of_critical hu hv hu0 hv0

example {u v : F → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : F) :
    fderiv ℝ (fun w => fderiv ℝ (fun y => u y - v y) w b) x a =
      fderiv ℝ (fun w => fderiv ℝ u w b) x a - fderiv ℝ (fun w => fderiv ℝ v w b) x a :=
  fderiv_fderiv_sub hu hv a b

end Critical

example {d : ℕ} {f : MinkowskiModel d →L[ℝ] ℝ} (h : ∀ c, f (Pi.single c 1) = 0) :
    f = 0 :=
  clm_eq_zero_of_single h

namespace CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

example (z : MinkowskiModel d) (i k l m : Fin (d + 1)) :
    ℝ :=
  superpotentialDensity g z i k l m

example (z : MinkowskiModel d) (i k l : Fin (d + 1)) :
    ℝ :=
  superpotential g z i k l

example (z : MinkowskiModel d) (i k : Fin (d + 1)) :
    ℝ :=
  raisedEinstein g z i k

example (z : MinkowskiModel d) (i k : Fin (d + 1)) :
    ℝ :=
  pseudotensor g z i k

example (z : MinkowskiModel d) (i k l m : Fin (d + 1)) :
    g.superpotentialDensity z i k l m = -g.superpotentialDensity z i l k m :=
  superpotentialDensity_antisymm g z i k l m

example (z : MinkowskiModel d) (i k l : Fin (d + 1)) :
    g.superpotential z i k l = -g.superpotential z i l k :=
  superpotential_antisymm g z i k l

example (i k l m : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun w => g.superpotentialDensity w i k l m) U :=
  contDiffOn_superpotentialDensity g i k l m

example (i k l : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun w => g.superpotential w i k l) U :=
  contDiffOn_superpotential g i k l

example {z : MinkowskiModel d} (hz : z ∈ U) (i : Fin (d + 1)) :
    ∑ k, fderiv ℝ (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w
      (Pi.single l 1)) z (Pi.single k 1) = 0 :=
  divergence_divergence_superpotential g hz i

example (x : MinkowskiModel d) (a b c e : Fin (d + 1)) :
    ℝ :=
  secondDerivative g x a b c e

variable {g} {x : MinkowskiModel d}

example (hx : x ∈ U) (a b c e : Fin (d + 1)) :
    g.secondDerivative x a b c e = g.secondDerivative x b a c e :=
  secondDerivative_symm_left hx a b c e

example (hx : x ∈ U) (a b c e : Fin (d + 1)) :
    g.secondDerivative x a b c e = g.secondDerivative x a b e c :=
  secondDerivative_symm_right hx a b c e

variable (hx : x ∈ U)
  (hc : ∀ a b c, fderiv ℝ (fun w => g.coefficient w a b) x (Pi.single c 1) = 0)

example (k i j : Fin (d + 1)) :
    christoffelOf g.coefficient x k i j = 0 :=
  christoffel_eq_zero_of_critical hc k i j

example (b c : Fin (d + 1)) :
    fderiv ℝ (fun z => (g.coefficient z)⁻¹ b c) x = 0 :=
  fderiv_coefficient_inv_eq_zero hx hc b c

example :
    fderiv ℝ (fun z => densityOf g.coefficient z) x = 0 :=
  fderiv_densityOf_eq_zero hx hc

example (k i j m : Fin (d + 1)) :
    fderiv ℝ (fun w => christoffelOf g.coefficient w k i j) x (Pi.single m 1) =
      ∑ l, (g.coefficient x)⁻¹ k l * (g.secondDerivative x j l m i +
        g.secondDerivative x l i m j - g.secondDerivative x i j m l) / 2 :=
  fderiv_christoffel_of_critical hx hc k i j m

example (b c l m : Fin (d + 1)) :
    fderiv ℝ (fun w => fderiv ℝ (fun v => (g.coefficient v)⁻¹ b c) w (Pi.single m 1)) x
        (Pi.single l 1) =
      -∑ a, ∑ e, (g.coefficient x)⁻¹ b a * (g.coefficient x)⁻¹ c e *
        g.secondDerivative x a e l m :=
  fderiv_fderiv_coefficient_inv hx hc b c l m

example (l m : Fin (d + 1)) :
    fderiv ℝ (fun w => fderiv ℝ (fun v => densityOf g.coefficient v) w (Pi.single m 1)) x
        (Pi.single l 1) =
      densityOf g.coefficient x *
        ((∑ c, ∑ e, (g.coefficient x)⁻¹ c e * g.secondDerivative x c e l m) / 2) :=
  fderiv_fderiv_densityOf hx hc l m

example (a b : Fin (d + 1)) :
    ricciOf g.coefficient x a b =
      ∑ c, ∑ e, (g.coefficient x)⁻¹ c e * (g.secondDerivative x b e c a +
        g.secondDerivative x e a c b - g.secondDerivative x a b c e -
        g.secondDerivative x c e a b) / 2 :=
  ricciOf_of_critical hx hc a b

example (i k : Fin (d + 1)) :
    ∑ a, ∑ b, (g.coefficient x)⁻¹ i a * (g.coefficient x)⁻¹ k b * g.coefficient x a b =
      (g.coefficient x)⁻¹ i k :=
  sum_inv_mul_coefficient hx i k

example (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) x (Pi.single l 1) =
      2 * densityOf g.coefficient x ^ 2 * g.raisedEinstein x i k :=
  divergence_superpotential_eq hx hc i k

example (i k : Fin (d + 1)) :
    g.pseudotensor x i k = 0 :=
  pseudotensor_eq_zero hx hc i k

example {κ : ℝ} {T : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {z : MinkowskiModel d}
    (hz : z ∈ U) (i : Fin (d + 1)) :
    ∑ k, fderiv ℝ (fun w => densityOf g.coefficient w ^ 2 *
      (κ * T w i k + g.pseudotensor w i k)) z (Pi.single k 1) = 0 :=
  divergence_total_eq_zero (g := g) hT hz i

example {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      ∑ l, fderiv ℝ (fun w => g.superpotential w k i l) z (Pi.single l 1) :=
  divergence_superpotential_symm (g := g) hz i k

example {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.raisedEinstein z i k = g.raisedEinstein z k i :=
  raisedEinstein_symm (g := g) hz i k

example {z : MinkowskiModel d} (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.pseudotensor z i k = g.pseudotensor z k i :=
  pseudotensor_symm (g := g) hz i k

end CoordinateMetric

end ProjectAinos.SmoothGeometry

open Finset

namespace ProjectAinos.SmoothGeometry

example {n : ℕ} (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hS₁ : ∀ a b c e, S a b c e = S b a c e)
    (hS₂ : ∀ a b c e, S a b c e = S a b e c) (i k : Fin n) :
    ∑ l, ∑ m, ((∑ c, ∑ d, G c d * S c d l m) * (G i k * G l m - G i l * G k m) +
        (-∑ a, ∑ e, G i a * G k e * S a e l m) * G l m +
        G i k * (-∑ a, ∑ e, G l a * G m e * S a e l m) -
        (-∑ a, ∑ e, G i a * G l e * S a e l m) * G k m -
        G i l * (-∑ a, ∑ e, G k a * G m e * S a e l m)) =
      2 * ∑ a, ∑ b, G i a * G k b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) -
        G i k * ∑ a, ∑ b, G a b *
          (∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2) :=
  pseudotensor_algebra G S hG hS₁ hS₂ i k

example {n : ℕ} (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hS₁ : ∀ a b c e, S a b c e = S b a c e) (b c l m : Fin n) :
    -∑ e, ((∑ a, G b a * (S e a l m + S a m l e - S m e l a) / 2) * G e c +
        (∑ a, G c a * (S e a l m + S a m l e - S m e l a) / 2) * G b e) =
      -∑ a, ∑ e, G b a * G c e * S a e l m :=
  inverse_second_algebra G S hG hS₁ b c l m

example {n : ℕ} (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hS₁ : ∀ a b c e, S a b c e = S b a c e) (l m : Fin n) :
    ∑ c, ∑ d, G c d * (S m d l c + S d c l m - S c m l d) / 2 =
      (∑ c, ∑ d, G c d * S c d l m) / 2 :=
  density_second_algebra G S hG hS₁ l m

example {n : ℕ} (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b, G a b = G b a) (hS₁ : ∀ a b c e, S a b c e = S b a c e)
    (hS₂ : ∀ a b c e, S a b c e = S a b e c) (a b : Fin n) :
    ∑ c, (∑ d, G c d * (S b d c a + S d a c b - S a b c d) / 2 -
        ∑ d, G c d * (S b d a c + S d c a b - S c b a d) / 2) =
      ∑ c, ∑ d, G c d * (S b d c a + S d a c b - S a b c d - S c d a b) / 2 :=
  ricci_algebra G S hG hS₁ hS₂ a b

end ProjectAinos.SmoothGeometry

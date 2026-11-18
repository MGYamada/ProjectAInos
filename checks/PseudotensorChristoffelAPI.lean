/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorChristoffel

/-! Public consumers of the expression (96.9) of the energy-momentum pseudotensor: the arrays
`H^{ikl}`, its derivative and the braces of (96.9), the reindexing of finite sums, the reduced
second derivatives and the identities of the superpotential, of the part linear in the second
derivatives and of the part quadratic in the Christoffel symbols; the derivative of `H` along
functions, the derivative of the Christoffel symbols and the Ricci tensor at every point, the
superpotential and its divergence in the Christoffel symbols, and the expression (96.9) itself.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

section Algebra

open Finset

variable {n : ℕ}

example (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (i k l : Fin n) :
    ℝ :=
  pseudoH G Γ i k l

example (G dG : Fin n → Fin n → ℝ) (Γ dΓ : Fin n → Fin n → Fin n → ℝ) (i k l : Fin n) :
    ℝ :=
  pseudoHDeriv G dG Γ dΓ i k l

example (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (i k : Fin n) :
    ℝ :=
  pseudoBraces G Γ i k

example (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ) (m k i j : Fin n) :
    ℝ :=
  christoffelDerivative G S m k i j

example (G : Fin n → Fin n → ℝ) (S : Fin n → Fin n → Fin n → Fin n → ℝ) (a b : Fin n) :
    ℝ :=
  ricciDerivative G S a b

example (C : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c e : Fin n) :
    ℝ :=
  reducedSecond C Γ S a b c e

example (f g : Fin n → Fin n → ℝ) (c : ℝ) (σ : Fin n × Fin n ≃ Fin n × Fin n)
    (h : ∀ p : Fin n × Fin n, f p.1 p.2 = c * g (σ p).1 (σ p).2) :
    ∑ a, ∑ b, f a b = c * ∑ a, ∑ b, g a b :=
  sum2_reindex f g c σ h

example (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d =
      ∑ p : Fin n × Fin n × Fin n × Fin n, f p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  sum4_eq_sum_prod f

example (f g : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ)
    (σ : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n)
    (h : ∀ p : Fin n × Fin n × Fin n × Fin n, f p.1 p.2.1 p.2.2.1 p.2.2.2 =
      c * g (σ p).1 (σ p).2.1 (σ p).2.2.1 (σ p).2.2.2) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = c * ∑ a, ∑ b, ∑ c, ∑ d, g a b c d :=
  sum4_reindex f g c σ h

example (G dG : Fin n → Fin n → ℝ) (Γ dΓ₁ dΓ₂ : Fin n → Fin n → Fin n → ℝ) (i k l : Fin n) :
    pseudoHDeriv G dG Γ (fun p q r => dΓ₁ p q r + dΓ₂ p q r) i k l =
      pseudoHDeriv G dG Γ dΓ₁ i k l + pseudoHDeriv G (fun _ _ => 0) Γ dΓ₂ i k l :=
  pseudoHDeriv_add G dG Γ dΓ₁ dΓ₂ i k l

section Reduced

variable {C : Fin n → Fin n → ℝ} {Γ : Fin n → Fin n → Fin n → ℝ}
  {S : Fin n → Fin n → Fin n → Fin n → ℝ}

example (hS : ∀ a b c e, S a b c e = S b a c e) (a b c e : Fin n) :
    reducedSecond C Γ S a b c e = reducedSecond C Γ S b a c e :=
  reducedSecond_symm_left hS a b c e

example (hC : ∀ a b, C a b = C b a) (hS : ∀ a b c e, S a b c e = S a b e c) (a b c e : Fin n) :
    reducedSecond C Γ S a b c e = reducedSecond C Γ S a b e c :=
  reducedSecond_symm_right hC hS a b c e

example (G : Fin n → Fin n → ℝ) (hΓ : ∀ a b c, Γ a b c = Γ a c b) (m k i j : Fin n) :
    christoffelDerivative G (reducedSecond C Γ S) m k i j =
      christoffelDerivative G S m k i j - ∑ l, G k l * ∑ p, ∑ q, C p q * Γ p m l * Γ q i j :=
  christoffelDerivative_reducedSecond G hΓ m k i j

end Reduced

example (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (i k l : Fin n) :
    ∑ m, (2 * (∑ c, Γ c c m) * (G i k * G l m - G i l * G k m) +
      ((-∑ e, (Γ i m e * G e k + Γ k m e * G i e)) * G l m +
        G i k * (-∑ e, (Γ l m e * G e m + Γ m m e * G l e)) -
        ((-∑ e, (Γ i m e * G e l + Γ l m e * G i e)) * G k m +
          G i l * (-∑ e, (Γ k m e * G e m + Γ m m e * G k e))))) = pseudoH G Γ i k l :=
  superpotential_algebra G Γ hG hΓ i k l

example (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hS₁ : ∀ a b c e, S a b c e = S b a c e) (hS₂ : ∀ a b c e, S a b c e = S a b e c)
    (i k : Fin n) :
    (∑ l, pseudoHDeriv G (fun _ _ => 0) Γ (christoffelDerivative G S l) i k l) / 2 =
      ∑ a, ∑ b, G i a * G k b * ricciDerivative G S a b -
        G i k * (∑ a, ∑ b, G a b * ricciDerivative G S a b) / 2 :=
  pseudotensor_second_algebra G Γ S hG hS₁ hS₂ i k

example (G : Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (i k : Fin n) :
    ∑ l, ∑ c, Γ c c l * pseudoH G Γ i k l +
      (∑ l, pseudoHDeriv G (fun a b => -∑ e, (Γ a l e * G e b + Γ b l e * G a e)) Γ
        (fun p q r => -∑ e, Γ p l e * Γ e q r) i k l) / 2 = pseudoBraces G Γ i k / 2 :=
  pseudotensor_quadratic G Γ hG hΓ i k

end Algebra

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {z : E}

example {a b c : E → ℝ} (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z)
    (hc : DifferentiableAt ℝ c z) (v : E) :
    fderiv ℝ (fun w => a w * b w * c w) z v =
      (fderiv ℝ a z v * b z + a z * fderiv ℝ b z v) * c z + a z * b z * fderiv ℝ c z v :=
  fderiv_mul_mul_apply ha hb hc v

variable {Gf : E → Fin n → Fin n → ℝ} {Γf : E → Fin n → Fin n → Fin n → ℝ}

example (hG : ∀ a b, DifferentiableAt ℝ (fun w => Gf w a b) z)
    (hΓ : ∀ a b c, DifferentiableAt ℝ (fun w => Γf w a b c) z) (i k l : Fin n) :
    DifferentiableAt ℝ (fun w => pseudoH (Gf w) (Γf w) i k l) z :=
  differentiableAt_pseudoH hG hΓ i k l

example (hG : ∀ a b, DifferentiableAt ℝ (fun w => Gf w a b) z)
    (hΓ : ∀ a b c, DifferentiableAt ℝ (fun w => Γf w a b c) z) (v : E) (i k l : Fin n) :
    fderiv ℝ (fun w => pseudoH (Gf w) (Γf w) i k l) z v =
      pseudoHDeriv (Gf z) (fun a b => fderiv ℝ (fun w => Gf w a b) z v) (Γf z)
        (fun a b c => fderiv ℝ (fun w => Γf w a b c) z v) i k l :=
  fderiv_pseudoH hG hΓ v i k l

end Derivative

namespace CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

example (x : MinkowskiModel d) (a b c e : Fin (d + 1)) :
    ℝ :=
  reducedSecondDerivative g x a b c e

variable {g} {z : MinkowskiModel d}

example (hz : z ∈ U) (a b c e : Fin (d + 1)) :
    g.reducedSecondDerivative z a b c e = g.reducedSecondDerivative z b a c e :=
  reducedSecondDerivative_symm_left hz a b c e

example (hz : z ∈ U) (a b c e : Fin (d + 1)) :
    g.reducedSecondDerivative z a b c e = g.reducedSecondDerivative z a b e c :=
  reducedSecondDerivative_symm_right hz a b c e

example (hz : z ∈ U) (l i j : Fin (d + 1)) :
    ∑ q, g.coefficient z l q * christoffelOf g.coefficient z q i j =
      (fderiv ℝ (fun w => g.coefficient w j l) z (Pi.single i 1) +
        fderiv ℝ (fun w => g.coefficient w l i) z (Pi.single j 1) -
        fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single l 1)) / 2 :=
  sum_coefficient_mul_christoffelOf hz l i j

example (hz : z ∈ U) (k i j m : Fin (d + 1)) :
    fderiv ℝ (fun w => christoffelOf g.coefficient w k i j) z (Pi.single m 1) =
      christoffelDerivative (fun a b => (g.coefficient z)⁻¹ a b) (g.reducedSecondDerivative z)
          m k i j -
        ∑ e, christoffelOf g.coefficient z k m e * christoffelOf g.coefficient z e i j :=
  fderiv_christoffelOf hz k i j m

example (hz : z ∈ U) (a b : Fin (d + 1)) :
    ricciOf g.coefficient z a b =
      ricciDerivative (fun p q => (g.coefficient z)⁻¹ p q) (g.reducedSecondDerivative z) a b :=
  ricciOf_eq hz a b

example (hz : z ∈ U) (i k l : Fin (d + 1)) :
    g.superpotential z i k l = densityOf g.coefficient z ^ 2 *
      pseudoH (fun a b => (g.coefficient z)⁻¹ a b) (christoffelOf g.coefficient z) i k l :=
  superpotential_eq hz i k l

example (hz : z ∈ U) (i k : Fin (d + 1)) :
    ∑ l, fderiv ℝ (fun w => g.superpotential w i k l) z (Pi.single l 1) =
      densityOf g.coefficient z ^ 2 *
        (2 * ∑ l, ∑ c, christoffelOf g.coefficient z c c l *
            pseudoH (fun a b => (g.coefficient z)⁻¹ a b) (christoffelOf g.coefficient z) i k l +
          ∑ l, pseudoHDeriv (fun a b => (g.coefficient z)⁻¹ a b)
            (fun a b => -∑ e, (christoffelOf g.coefficient z a l e * (g.coefficient z)⁻¹ e b +
              christoffelOf g.coefficient z b l e * (g.coefficient z)⁻¹ a e))
            (christoffelOf g.coefficient z)
            (fun p q r => fderiv ℝ (fun w => christoffelOf g.coefficient w p q r) z
              (Pi.single l 1)) i k l) :=
  divergence_superpotential_christoffel hz i k

example (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.raisedEinstein z i k = ∑ a, ∑ b, (g.coefficient z)⁻¹ i a * (g.coefficient z)⁻¹ k b *
      ricciOf g.coefficient z a b - (g.coefficient z)⁻¹ i k *
        (∑ a, ∑ b, (g.coefficient z)⁻¹ a b * ricciOf g.coefficient z a b) / 2 :=
  raisedEinstein_eq hz i k

example (hz : z ∈ U) (i k : Fin (d + 1)) :
    g.pseudotensor z i k = pseudoBraces (fun a b => (g.coefficient z)⁻¹ a b)
      (christoffelOf g.coefficient z) i k / 2 :=
  pseudotensor_eq hz i k

end CoordinateMetric

end ProjectAinos.SmoothGeometry

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.Mechanics.Separation.Coordinates

/-! Typed contracts for the separation of the variables: a Hamiltonian of
Stäckel's form on a box, the separated action with its derivatives, the
Hamilton–Jacobi equation, the completeness of the integral, Jacobi's theorem,
and spherical, parabolic and elliptic co-ordinates. These examples use default
elaborator options. -/

open ProjectAInos ProjectAInos.Mechanics ProjectAInos.Mechanics.Stackel
open Set Filter MeasureTheory
open scoped Topology Real

noncomputable section

section Stackel

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : System ι}
variable {ε c q α : ι → ℝ} {i j : ι} {x t : ℝ} {Q : ι → ℝ → ℝ} {Q' β : ι → ℝ}

example (i : ι) : IsOpen (s.I i) := s.isOpen i

example (i : ι) : (s.I i).OrdConnected := s.ordConnected i

example (i j : ι) : ContDiffOn ℝ 1 (s.φ i j) (s.I i) := s.contDiffOn_φ i j

example (i : ι) : ContDiffOn ℝ 1 (s.g i) (s.I i) := s.contDiffOn_g i

example (i : ι) : ContDiffOn ℝ 1 (s.u i) (s.I i) := s.contDiffOn_u i

example (i : ι) {x : ℝ} (hx : x ∈ s.I i) : 0 < s.g i x := s.g_pos i x hx

example {q : ι → ℝ} (hq : ∀ i, q i ∈ s.I i) (j : ι) :
    ∑ i, s.Ψ i q * s.φ i j (q i) = if j = s.j₀ then 1 else 0 := s.sum_Ψ q hq j

example {q : ι → ℝ} (hq : ∀ i, q i ∈ s.I i) (i : ι) : DifferentiableAt ℝ (s.Ψ i) q :=
  s.differentiableAt_Ψ q hq i

example : s.domain = {q | ∀ i, q i ∈ s.I i} := rfl

example (q p : ι → ℝ) :
    s.hamiltonian q p = ∑ i, s.Ψ i q * (s.g i (q i) * p i ^ 2 / 2 + s.u i (q i)) := rfl

example (i : ι) (x : ℝ) (α : ι → ℝ) :
    s.radicand i x α = 2 * (∑ j, s.φ i j x * α j - s.u i x) / s.g i x := rfl

example (ε : ι → ℝ) (i : ι) (x : ℝ) (α : ι → ℝ) :
    s.momentum ε i x α = ε i * √(s.radicand i x α) := rfl

example (c : ι → ℝ) (i : ι) (x : ℝ) (α : ι → ℝ) :
    s.partialAction c i x α = ∫ y in c i..x, √(s.radicand i y α) := rfl

example (c : ι → ℝ) (i j : ι) (x : ℝ) (α : ι → ℝ) :
    s.angleIntegral c i j x α =
      ∫ y in c i..x, s.φ i j y / (s.g i y * √(s.radicand i y α)) := rfl

example (ε c q α : ι → ℝ) (t : ℝ) :
    s.action ε c q α t = -(α s.j₀ * t) + ∑ i, ε i * s.partialAction c i (q i) α := rfl

example (J : ι → Set ℝ) (hJo : ∀ i, IsOpen (J i)) (hJc : ∀ i, (J i).OrdConnected)
    (hJ : ∀ i, J i ⊆ s.I i) : (s.restrict J hJo hJc hJ).I = J := rfl

example (J : ι → Set ℝ) (hJo : ∀ i, IsOpen (J i))
    (hJc : ∀ i, (J i).OrdConnected) (hJ : ∀ i, J i ⊆ s.I i) :
    (s.restrict J hJo hJc hJ).hamiltonian = s.hamiltonian :=
  System.restrict_hamiltonian s J hJo hJc hJ

example (J : ι → Set ℝ) (hJo : ∀ i, IsOpen (J i))
    (hJc : ∀ i, (J i).OrdConnected) (hJ : ∀ i, J i ⊆ s.I i) :
    (s.restrict J hJo hJc hJ).radicand = s.radicand :=
  System.restrict_radicand s J hJo hJc hJ

example (f α : ι → ℝ) (j : ι) (a : ℝ) :
    ∑ k, f k * Function.update α j a k = ∑ k, f k * α k + f j * (a - α j) :=
  System.sum_mul_update f α j a

example (i j : ι) (x : ℝ) (α : ι → ℝ) (a : ℝ) :
    s.radicand i x (Function.update α j a) =
      s.radicand i x α + 2 * s.φ i j x * (a - α j) / s.g i x :=
  System.radicand_update i j x α a

example (hε : ∀ i, ε i ^ 2 = 1) (hx : x ∈ s.I i)
    (hR : 0 ≤ s.radicand i x α) :
    s.g i x * s.momentum ε i x α ^ 2 / 2 + s.u i x = ∑ j, s.φ i j x * α j :=
  System.separated_equation hε hx hR

example (hε : ∀ i, ε i ^ 2 = 1) (hq : q ∈ s.domain)
    (hR : ∀ i, 0 ≤ s.radicand i (q i) α) :
    s.hamiltonian q (fun i => s.momentum ε i (q i) α) = α s.j₀ :=
  System.hamiltonian_momentum hε hq hR

example (i : ι) (α : ι → ℝ) :
    ContDiffOn ℝ 1 (fun x => s.radicand i x α) (s.I i) :=
  System.contDiffOn_radicand i α

example (i : ι) (α : ι → ℝ) :
    ContinuousOn (fun x => √(s.radicand i x α)) (s.I i) :=
  System.continuousOn_sqrt_radicand i α

example (hc : c i ∈ s.I i) (hx : x ∈ s.I i) :
    HasDerivAt (fun x => s.partialAction c i x α) (√(s.radicand i x α)) x :=
  System.hasDerivAt_partialAction hc hx

example (i j : ι) {α : ι → ℝ}
    (hR : ∀ x ∈ s.I i, 0 < s.radicand i x α) :
    ContinuousOn (fun x => s.φ i j x / (s.g i x * √(s.radicand i x α))) (s.I i) :=
  System.continuousOn_angle_integrand i j hR

example (hc : c i ∈ s.I i) (hx : x ∈ s.I i)
    (hR : ∀ x ∈ s.I i, 0 < s.radicand i x α) (j : ι) :
    HasDerivAt (fun x => s.angleIntegral c i j x α)
      (s.φ i j x / (s.g i x * √(s.radicand i x α))) x :=
  System.hasDerivAt_angleIntegral hc hx hR j

example (hc : c i ∈ s.I i) (hx : x ∈ s.I i)
    (hR : ∀ x ∈ s.I i, 0 < s.radicand i x α) (j : ι) :
    HasDerivAt (fun a => s.partialAction c i x (Function.update α j a))
      (s.angleIntegral c i j x α) (α j) :=
  System.hasDerivAt_partialAction_param hc hx hR j

example (ε c q α : ι → ℝ) (t : ℝ) (i : ι) (x : ℝ) :
    s.action ε c (Function.update q i x) α t =
      s.action ε c q α t +
        ε i * (s.partialAction c i x α - s.partialAction c i (q i) α) :=
  System.action_update ε c q α t i x

example (hc : c i ∈ s.I i) (hq : q i ∈ s.I i) (t : ℝ) :
    HasDerivAt (fun x => s.action ε c (Function.update q i x) α t)
      (s.momentum ε i (q i) α) (q i) :=
  System.hasDerivAt_action_position hc hq t

example (ε c q α : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun τ => s.action ε c q α τ) (-α s.j₀) t :=
  System.hasDerivAt_action_time ε c q α t

example (hc : ∀ i, c i ∈ s.I i) (hq : q ∈ s.domain)
    (hR : ∀ i, ∀ x ∈ s.I i, 0 < s.radicand i x α) (ε : ι → ℝ) (t : ℝ) (j : ι) :
    HasDerivAt (fun a => s.action ε c q (Function.update α j a) t)
      (-((if j = s.j₀ then 1 else 0) * t) + ∑ i, ε i * s.angleIntegral c i j (q i) α)
      (α j) :=
  System.hasDerivAt_action_param hc hq hR ε t j

example (hε : ∀ i, ε i ^ 2 = 1) (hq : q ∈ s.domain)
    (hR : ∀ i, 0 < s.radicand i (q i) α)
    (hdet : (Matrix.of fun i j => s.φ i j (q i)).det ≠ 0) :
    (Matrix.of fun i j =>
      ε i * (s.φ i j (q i) / (s.g i (q i) * √(s.radicand i (q i) α)))).det ≠ 0 :=
  System.det_mixed_ne_zero hε hq hR hdet

example (q p : ι → ℝ) (i : ι) (y : ℝ) :
    s.hamiltonian q (Function.update p i y) =
      s.hamiltonian q p + s.Ψ i q * (s.g i (q i) * (y ^ 2 - p i ^ 2) / 2) :=
  System.hamiltonian_update_momentum q p i y

example (q p : ι → ℝ) (i : ι) :
    HasDerivAt (fun y => s.hamiltonian q (Function.update p i y))
      (s.Ψ i q * s.g i (q i) * p i) (p i) :=
  System.hasDerivAt_hamiltonian_momentum q p i

example (hε : ∀ i, ε i ^ 2 = 1) (hc : ∀ i, c i ∈ s.I i)
    (hR : ∀ i, ∀ x ∈ s.I i, 0 < s.radicand i x α)
    (hQ : ∀ i, HasDerivAt (Q i) (Q' i) t) (hD : (fun i => Q i t) ∈ s.domain)
    (hJ : ∀ j, ∀ᶠ τ in 𝓝 t, -((if j = s.j₀ then 1 else 0) * τ) +
      ∑ i, ε i * s.angleIntegral c i j (Q i τ) α = β j)
    (hdet : (Matrix.of fun i j => s.φ i j (Q i t)).det ≠ 0) (i : ι) :
    Q' i = s.Ψ i (fun k => Q k t) * s.g i (Q i t) * s.momentum ε i (Q i t) α :=
  System.eq_of_jacobi hε hc hR hQ hD hJ hdet i

example (hε : ∀ i, ε i ^ 2 = 1)
    (hR : ∀ i, ∀ x ∈ s.I i, 0 < s.radicand i x α) (hD : (fun i => Q i t) ∈ s.domain) (i : ι)
    (hQ : HasDerivAt (Q i) (Q' i) t)
    (hvel : Q' i = s.Ψ i (fun k => Q k t) * s.g i (Q i t) * s.momentum ε i (Q i t) α)
    {D : ℝ} (hH : HasDerivAt (fun x => s.hamiltonian (Function.update (fun k => Q k t) i x)
      (fun k => s.momentum ε k (Q k t) α)) D (Q i t)) :
    HasDerivAt (fun τ => s.momentum ε i (Q i τ) α) (-D) t :=
  System.hasDerivAt_momentum_of_jacobi hε hR hD i hQ hvel hH

end Stackel

section Coordinates

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : System ι}
variable {r θ φ ξ η : ℝ → ℝ} {r' θ' φ' ξ' η' t : ℝ} {m : ℝ} {a b c : ℝ → ℝ}

example (q v : ι → ℝ) :
    s.kinetic q v = ∑ i, v i ^ 2 / (2 * (s.Ψ i q * s.g i (q i))) := rfl

example (q : ι → ℝ) : s.potential q = ∑ i, s.Ψ i q * s.u i (q i) := rfl

example {q v : ι → ℝ} (hΨ : ∀ i, s.Ψ i q ≠ 0)
    (hg : ∀ i, s.g i (q i) ≠ 0) :
    s.hamiltonian q (fun i => v i / (s.Ψ i q * s.g i (q i))) =
      ∑ i, v i / (s.Ψ i q * s.g i (q i)) * v i - (s.kinetic q v - s.potential q) :=
  System.hamiltonian_eq_legendre s hΨ hg

example {ρ φ : ℝ → ℝ} {ρ' φ' t : ℝ} (hρ : HasDerivAt ρ ρ' t)
    (hφ : HasDerivAt φ φ' t) :
    ∃ x' y' : ℝ, HasDerivAt (fun s => ρ s * Real.cos (φ s)) x' t ∧
      HasDerivAt (fun s => ρ s * Real.sin (φ s)) y' t ∧
      x' ^ 2 + y' ^ 2 = ρ' ^ 2 + ρ t ^ 2 * φ' ^ 2 :=
  cylindrical_speed_sq hρ hφ

example (hr : HasDerivAt r r' t) (hθ : HasDerivAt θ θ' t) :
    ∃ ρ' z' : ℝ, HasDerivAt (fun s => r s * Real.sin (θ s)) ρ' t ∧
      HasDerivAt (fun s => r s * Real.cos (θ s)) z' t ∧
      ρ' ^ 2 + z' ^ 2 = r' ^ 2 + r t ^ 2 * θ' ^ 2 :=
  spherical_kinetic hr hθ

example (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t) (hξ0 : 0 < ξ t)
    (hη0 : 0 < η t) :
    ∃ ρ' z' : ℝ, HasDerivAt (fun s => √(ξ s * η s)) ρ' t ∧
      HasDerivAt (fun s => (ξ s - η s) / 2) z' t ∧
      ρ' ^ 2 + z' ^ 2 = (ξ t + η t) / (4 * ξ t) * ξ' ^ 2 + (ξ t + η t) / (4 * η t) * η' ^ 2 :=
  parabolic_kinetic hξ hη hξ0 hη0

example (σ : ℝ) (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t)
    (hξ1 : 1 < ξ t) (hη1 : η t ∈ Ioo (-1 : ℝ) 1) :
    ∃ ρ' z' : ℝ, HasDerivAt (fun s => σ * √((ξ s ^ 2 - 1) * (1 - η s ^ 2))) ρ' t ∧
      HasDerivAt (fun s => σ * (ξ s * η s)) z' t ∧
      ρ' ^ 2 + z' ^ 2 = σ ^ 2 * (ξ t ^ 2 - η t ^ 2) / (ξ t ^ 2 - 1) * ξ' ^ 2 +
        σ ^ 2 * (ξ t ^ 2 - η t ^ 2) / (1 - η t ^ 2) * η' ^ 2 :=
  elliptic_kinetic σ hξ hη hξ1 hη1

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0)) (hb : ContDiffOn ℝ 1 b (Ioo 0 π))
    (hc : ContDiffOn ℝ 1 c univ) :
    (spherical hm ha hb hc).I = ![Ioi 0, Ioo 0 π, univ] ∧ (spherical hm ha hb hc).j₀ = 0 ∧
      (spherical hm ha hb hc).u = ![a, b, c] :=
  ⟨rfl, rfl, rfl⟩

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q p : Fin 3 → ℝ) :
    (spherical hm ha hb hc).hamiltonian q p =
      p 0 ^ 2 / (2 * m) + a (q 0) + (p 1 ^ 2 / (2 * m) + b (q 1)) / q 0 ^ 2 +
        (p 2 ^ 2 / (2 * m) + c (q 2)) / (q 0 ^ 2 * Real.sin (q 1) ^ 2) :=
  hamiltonian_spherical hm ha hb hc q p

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q v : Fin 3 → ℝ) :
    (spherical hm ha hb hc).kinetic q v =
      m / 2 * (v 0 ^ 2 + q 0 ^ 2 * v 1 ^ 2 + q 0 ^ 2 * Real.sin (q 1) ^ 2 * v 2 ^ 2) :=
  kinetic_spherical hm ha hb hc q v

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (spherical hm ha hb hc).φ i j (q i)).det = 1 :=
  det_spherical hm ha hb hc q

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0)) (hb : ContDiffOn ℝ 1 b (Ioi 0))
    (hc : ContDiffOn ℝ 1 c univ) :
    (parabolic hm ha hb hc).I = ![Ioi 0, Ioi 0, univ] ∧ (parabolic hm ha hb hc).j₀ = 0 ∧
      (parabolic hm ha hb hc).u = ![a, b, c] :=
  ⟨rfl, rfl, rfl⟩

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) (q p : Fin 3 → ℝ) :
    (parabolic hm ha hb hc).hamiltonian q p =
      (2 * q 0 * p 0 ^ 2 / m + a (q 0) + (2 * q 1 * p 1 ^ 2 / m + b (q 1))) / (q 0 + q 1) +
        (p 2 ^ 2 / (2 * m) + c (q 2)) / (q 0 * q 1) :=
  hamiltonian_parabolic hm ha hb hc q p

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (h0 : 0 < q 0) (h1 : 0 < q 1) (v : Fin 3 → ℝ) :
    (parabolic hm ha hb hc).kinetic q v =
      m / 2 * ((q 0 + q 1) / (4 * q 0) * v 0 ^ 2 + (q 0 + q 1) / (4 * q 1) * v 1 ^ 2 +
        q 0 * q 1 * v 2 ^ 2) :=
  kinetic_parabolic hm ha hb hc h0 h1 v

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (parabolic hm ha hb hc).φ i j (q i)).det = -(q 0 + q 1) :=
  det_parabolic hm ha hb hc q

example {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) :
    (elliptic hm hσ ha hb hc).I = ![Ioi 1, Ioo (-1) 1, univ] ∧
      (elliptic hm hσ ha hb hc).j₀ = 0 ∧ (elliptic hm hσ ha hb hc).u = ![a, b, c] :=
  ⟨rfl, rfl, rfl⟩

example {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) (q p : Fin 3 → ℝ) :
    (elliptic hm hσ ha hb hc).hamiltonian q p =
      ((q 0 ^ 2 - 1) * p 0 ^ 2 / (2 * m * σ ^ 2) + a (q 0) +
          ((1 - q 1 ^ 2) * p 1 ^ 2 / (2 * m * σ ^ 2) + b (q 1))) / (q 0 ^ 2 - q 1 ^ 2) +
        (p 2 ^ 2 / (2 * m) + c (q 2)) / (σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2)) :=
  hamiltonian_elliptic hm hσ ha hb hc q p

example {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (h0 : 1 < q 0) (h1 : q 1 ∈ Ioo (-1 : ℝ) 1) (v : Fin 3 → ℝ) :
    (elliptic hm hσ ha hb hc).kinetic q v =
      m / 2 * (σ ^ 2 * (q 0 ^ 2 - q 1 ^ 2) / (q 0 ^ 2 - 1) * v 0 ^ 2 +
        σ ^ 2 * (q 0 ^ 2 - q 1 ^ 2) / (1 - q 1 ^ 2) * v 1 ^ 2 +
        σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2) * v 2 ^ 2) :=
  kinetic_elliptic hm hσ ha hb hc h0 h1 v

example {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (elliptic hm hσ ha hb hc).φ i j (q i)).det =
      -(q 0 ^ 2 - q 1 ^ 2) :=
  det_elliptic hm hσ ha hb hc q

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (spherical hm ha hb hc).φ i j (q i)).det ≠ 0 :=
  det_ne_zero_spherical hm ha hb hc q

example (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (hq : q ∈ (parabolic hm ha hb hc).domain) :
    (Matrix.of fun i j => (parabolic hm ha hb hc).φ i j (q i)).det ≠ 0 :=
  det_ne_zero_parabolic hm ha hb hc hq

example {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : ContDiffOn ℝ 1 a (Ioi 1)) (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1))
    (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (hq : q ∈ (elliptic hm hσ ha hb hc).domain) :
    (Matrix.of fun i j => (elliptic hm hσ ha hb hc).φ i j (q i)).det ≠ 0 :=
  det_ne_zero_elliptic hm hσ ha hb hc hq

example (hm : 0 < m) (i : Fin 3) (x : ℝ)
    (hx : x ∈ (![Ioi 1, Ioi 1, univ] : Fin 3 → Set ℝ) i) :
    0 < (parabolic (a := fun _ => 0) (b := fun _ => 0) (c := fun _ => 0) hm contDiffOn_const
      contDiffOn_const contDiffOn_const).radicand i x ![1, 0, 1] :=
  radicand_pos_parabolic_free hm i x hx

end Coordinates

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.Static
import ProjectAinos.GeneralRelativity.NewtonianFieldLimit

/-! Public consumers of the Newtonian limit of the field equations (Landau–Lifshitz §99): static
coefficients with their Christoffel symbols and `R₀₀ = N Δ_γ N`, the trace-reversed Einstein
equations, the static weak-field families with the exact identity for `ΔΦ − 4πGρ`, its bound of
order `ε`, the limit corollary, the corollary from the Einstein equations and the instances.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section Static

open Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {n : ℕ}

example :
    MinkowskiModel (n + 1) →L[ℝ] (Fin (n + 1) → ℝ) :=
  spatialProjection n

example (z : MinkowskiModel (n + 1)) :
    Fin (n + 1) → ℝ :=
  spatialPoint z

example :
    (spatialPoint : MinkowskiModel (n + 1) → Fin (n + 1) → ℝ) = spatialProjection n :=
  spatialPoint_eq_spatialProjection

example (z : MinkowskiModel (n + 1)) (α : Fin (n + 1)) :
    spatialPoint z α = z α.succ :=
  spatialPoint_apply z α

example :
    spatialPoint (Pi.single 0 1 : MinkowskiModel (n + 1)) = 0 :=
  spatialPoint_single_zero

example (α : Fin (n + 1)) :
    spatialPoint (Pi.single α.succ 1 : MinkowskiModel (n + 1)) = Pi.single α 1 :=
  spatialPoint_single_succ α

example (t : ℝ) (x : Fin (n + 1) → ℝ) :
    spatialPoint (Fin.cons t x : MinkowskiModel (n + 1)) = x :=
  spatialPoint_cons t x

example {f : (Fin (n + 1) → ℝ) → ℝ} {z : MinkowskiModel (n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPoint z)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => f (spatialPoint w)) z v =
      fderiv ℝ f (spatialPoint z) (spatialPoint v) :=
  fderiv_comp_spatialPoint hf v

example {f : (Fin (n + 1) → ℝ) → ℝ} {z : MinkowskiModel (n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPoint z)) :
    fderiv ℝ (fun w => f (spatialPoint w)) z (Pi.single 0 1) = 0 :=
  fderiv_comp_spatialPoint_zero hf

example {f : (Fin (n + 1) → ℝ) → ℝ} {z : MinkowskiModel (n + 1)}
    (hf : DifferentiableAt ℝ f (spatialPoint z)) (α : Fin (n + 1)) :
    fderiv ℝ (fun w => f (spatialPoint w)) z (Pi.single α.succ 1) =
      fderiv ℝ f (spatialPoint z) (Pi.single α 1) :=
  fderiv_comp_spatialPoint_succ hf α

example (N : (Fin (n + 1) → ℝ) → ℝ) (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : MinkowskiModel (n + 1)) :
    Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ :=
  staticCoefficient N γ z

variable {N : (Fin (n + 1) → ℝ) → ℝ}
  {γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

example (z : MinkowskiModel (n + 1)) :
    staticCoefficient N γ z 0 0 = -N (spatialPoint z) ^ 2 :=
  staticCoefficient_zero_zero z

example (z : MinkowskiModel (n + 1)) (β : Fin (n + 1)) :
    staticCoefficient N γ z 0 β.succ = 0 :=
  staticCoefficient_zero_succ z β

example (z : MinkowskiModel (n + 1)) (α : Fin (n + 1)) :
    staticCoefficient N γ z α.succ 0 = 0 :=
  staticCoefficient_succ_zero z α

example (z : MinkowskiModel (n + 1)) (α β : Fin (n + 1)) :
    staticCoefficient N γ z α.succ β.succ = γ (spatialPoint z) α β :=
  staticCoefficient_succ_succ z α β

example (N : (Fin (n + 1) → ℝ) → ℝ) (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : MinkowskiModel (n + 1)) :
    Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ :=
  staticInverse N γ z

example {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
    (hγ : (γ (spatialPoint z)).det ≠ 0) :
    (staticCoefficient N γ z)⁻¹ = staticInverse N γ z :=
  staticCoefficient_inv hN hγ

section Inverse

variable {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
  (hγ : (γ (spatialPoint z)).det ≠ 0)

include hN hγ

example :
    (staticCoefficient N γ z)⁻¹ 0 0 = -(N (spatialPoint z) ^ 2)⁻¹ :=
  staticCoefficient_inv_zero_zero hN hγ

example (β : Fin (n + 1)) :
    (staticCoefficient N γ z)⁻¹ 0 β.succ = 0 :=
  staticCoefficient_inv_zero_succ hN hγ β

example (α : Fin (n + 1)) :
    (staticCoefficient N γ z)⁻¹ α.succ 0 = 0 :=
  staticCoefficient_inv_succ_zero hN hγ α

example (α β : Fin (n + 1)) :
    (staticCoefficient N γ z)⁻¹ α.succ β.succ = (γ (spatialPoint z))⁻¹ α β :=
  staticCoefficient_inv_succ_succ hN hγ α β

end Inverse

section Derivatives

variable {z : MinkowskiModel (n + 1)}

example (hN : DifferentiableAt ℝ N (spatialPoint z)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w 0 0) z v =
      -(2 * N (spatialPoint z) * fderiv ℝ N (spatialPoint z) (spatialPoint v)) :=
  fderiv_staticCoefficient_zero_zero hN v

example (β : Fin (n + 1)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w 0 β.succ) z v = 0 :=
  fderiv_staticCoefficient_zero_succ β v

example (α : Fin (n + 1)) (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w α.succ 0) z v = 0 :=
  fderiv_staticCoefficient_succ_zero α v

example (α β : Fin (n + 1)) (hγ : DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z))
    (v : MinkowskiModel (n + 1)) :
    fderiv ℝ (fun w => staticCoefficient N γ w α.succ β.succ) z v =
      fderiv ℝ (fun y => γ y α β) (spatialPoint z) (spatialPoint v) :=
  fderiv_staticCoefficient_succ_succ α β hγ v

end Derivatives

section Christoffel

variable {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
  (hγ : (γ (spatialPoint z)).det ≠ 0)

include hN hγ

example (hNd : DifferentiableAt ℝ N (spatialPoint z)) :
    christoffelOf (staticCoefficient N γ) z 0 0 0 = 0 :=
  christoffelOf_staticCoefficient_zero_zero_zero hN hγ hNd

example (hNd : DifferentiableAt ℝ N (spatialPoint z)) (α : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z 0 0 α.succ =
      fderiv ℝ N (spatialPoint z) (Pi.single α 1) / N (spatialPoint z) :=
  christoffelOf_staticCoefficient_zero_zero_succ hN hγ hNd α

example (hNd : DifferentiableAt ℝ N (spatialPoint z)) (α : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z 0 α.succ 0 =
      fderiv ℝ N (spatialPoint z) (Pi.single α 1) / N (spatialPoint z) :=
  christoffelOf_staticCoefficient_zero_succ_zero hN hγ hNd α

example (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (α β : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z 0 α.succ β.succ = 0 :=
  christoffelOf_staticCoefficient_zero_succ_succ hN hγ hγd α β

example (hNd : DifferentiableAt ℝ N (spatialPoint z)) (μ : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ 0 0 =
      N (spatialPoint z) * ∑ ν, (γ (spatialPoint z))⁻¹ μ ν *
        fderiv ℝ N (spatialPoint z) (Pi.single ν 1) :=
  christoffelOf_staticCoefficient_succ_zero_zero hN hγ hNd μ

example (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (μ β : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ 0 β.succ = 0 :=
  christoffelOf_staticCoefficient_succ_zero_succ hN hγ hγd μ β

example (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z)) (μ α : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ α.succ 0 = 0 :=
  christoffelOf_staticCoefficient_succ_succ_zero hN hγ hγd μ α

example (hγd : ∀ α β, DifferentiableAt ℝ (fun y => γ y α β) (spatialPoint z))
    (μ α β : Fin (n + 1)) :
    christoffelOf (staticCoefficient N γ) z μ.succ α.succ β.succ =
      christoffelOf γ (spatialPoint z) μ α β :=
  christoffelOf_staticCoefficient_succ_succ_succ hN hγ hγd μ α β

end Christoffel

section SpatialInverse

variable {V : Set (Fin (n + 1) → ℝ)}

example (hV : IsOpen V) (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ V) (hdet : (γ x).det ≠ 0) (a b : Fin (n + 1)) :
    ContDiffAt ℝ ∞ (fun y => (γ y)⁻¹ a b) x :=
  contDiffAt_spatialInverse hV hγs hx hdet a b

example (hV : IsOpen V) (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V)
    (hdet : ∀ x ∈ V, (γ x).det ≠ 0) {x : Fin (n + 1) → ℝ} (hx : x ∈ V) (a b : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun y => (γ y)⁻¹ a b) x v =
      -∑ μ, ∑ ν, (γ x)⁻¹ a μ * fderiv ℝ (fun y => γ y μ ν) x v * (γ x)⁻¹ ν b :=
  fderiv_spatialInverse hV hγs hdet hx a b v

example (hV : IsOpen V) (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V)
    (hdet : ∀ x ∈ V, (γ x).det ≠ 0) (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ V) (a b c : Fin (n + 1)) :
    fderiv ℝ (fun y => (γ y)⁻¹ b c) x (Pi.single a 1) =
      -∑ μ, (christoffelOf γ x b a μ * (γ x)⁻¹ μ c +
        christoffelOf γ x c a μ * (γ x)⁻¹ b μ) :=
  fderiv_spatialInverse_eq_christoffel hV hγs hdet hsymm hx a b c

end SpatialInverse

example (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    ℝ :=
  spatialLaplacian γ f x

section Laplacian

variable {V : Set (Fin (n + 1) → ℝ)}

example (hV : IsOpen V) (hγs : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V)
    (hdet : ∀ x ∈ V, (γ x).det ≠ 0) (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f V) {x : Fin (n + 1) → ℝ} (hx : x ∈ V) :
    ∑ α, fderiv ℝ (fun y => ∑ β, (γ y)⁻¹ α β * fderiv ℝ f y (Pi.single β 1)) x
        (Pi.single α 1) +
      ∑ α, ∑ μ, christoffelOf γ x α α μ *
        ∑ β, (γ x)⁻¹ μ β * fderiv ℝ f x (Pi.single β 1) =
      spatialLaplacian γ f x :=
  divergence_eq_spatialLaplacian hV hγs hdet hsymm hf hx

end Laplacian

namespace IsStaticRegularOn

variable {V : Set (Fin (n + 1) → ℝ)} (h : IsStaticRegularOn N γ V)

include h

example {x : Fin (n + 1) → ℝ} (hx : x ∈ V) :
    DifferentiableAt ℝ N x :=
  lapse_differentiableAt h hx

example {x : Fin (n + 1) → ℝ} (hx : x ∈ V) (α β : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => γ y α β) x :=
  spatial_differentiableAt h hx α β

end IsStaticRegularOn

example {V : Set (Fin (n + 1) → ℝ)} (h : IsStaticRegularOn N γ V) {z : MinkowskiModel (n + 1)}
    (hz : spatialPoint z ∈ V) :
    ricciOf (staticCoefficient N γ) z 0 0 =
      N (spatialPoint z) * spatialLaplacian γ N (spatialPoint z) :=
  ricciOf_staticCoefficient_zero_zero h hz

example (V : Opens (Fin (n + 1) → ℝ)) :
    Opens (MinkowskiModel (n + 1)) :=
  staticDomain V

example {V : Opens (Fin (n + 1) → ℝ)} {z : MinkowskiModel (n + 1)} :
    z ∈ staticDomain V ↔ spatialPoint z ∈ V :=
  mem_staticDomain

example {z : MinkowskiModel (n + 1)}
    (hsymm : ∀ α β, γ (spatialPoint z) α β = γ (spatialPoint z) β α) (i k : Fin (n + 1 + 1)) :
    staticCoefficient N γ z i k = staticCoefficient N γ z k i :=
  staticCoefficient_symm hsymm i k

example {V : Opens (Fin (n + 1) → ℝ)} (hN : ContDiffOn ℝ ∞ N V)
    (hγ : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (i k : Fin (n + 1 + 1)) :
    ContDiffOn ℝ ∞ (fun z => staticCoefficient N γ z i k) (staticDomain V) :=
  contDiffOn_staticCoefficient hN hγ i k

example (N : (Fin (n + 1) → ℝ) → ℝ) (γ : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (V : Opens (Fin (n + 1) → ℝ)) (hN : ContDiffOn ℝ ∞ N V)
    (hγ : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hN0 : ∀ x ∈ V, N x ≠ 0)
    (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α)
    (hpos : ∀ x ∈ V, ∀ v : Fin (n + 1) → ℝ, v ≠ 0 → 0 < ∑ α, ∑ β, γ x α β * v α * v β) :
    CoordinateMetric .timeNegative (n + 1) (staticDomain V) :=
  staticMetric N γ V hN hγ hN0 hsymm hpos

example (V : Opens (Fin (n + 1) → ℝ)) (hN : ContDiffOn ℝ ∞ N V)
    (hγ : ∀ α β, ContDiffOn ℝ ∞ (fun x => γ x α β) V) (hN0 : ∀ x ∈ V, N x ≠ 0)
    (hsymm : ∀ x ∈ V, ∀ α β, γ x α β = γ x β α)
    (hpos : ∀ x ∈ V, ∀ v : Fin (n + 1) → ℝ, v ≠ 0 → 0 < ∑ α, ∑ β, γ x α β * v α * v β) :
    (staticMetric N γ V hN hγ hN0 hsymm hpos).coefficient = staticCoefficient N γ :=
  coefficient_staticMetric V hN hγ hN0 hsymm hpos

example (v : Fin (n + 1) → ℝ) (hv : v ≠ 0) :
    0 < ∑ α, ∑ β, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) α β * v α * v β :=
  one_spatial_pos v hv

example :
    CoordinateMetric .timeNegative (n + 1) (staticDomain ⊤) :=
  minkowskiStatic n

example :
    CoordinateMetric .timeNegative (n + 1) (staticDomain ⊤) :=
  expLapseStatic n

example (y v : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun x : Fin (n + 1) → ℝ => Real.exp (x 0)) y v = Real.exp (y 0) * v 0 :=
  fderiv_exp_apply_zero y v

example :
    IsStaticRegularOn (fun x : Fin (n + 1) → ℝ => Real.exp (x 0))
      (fun _ => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) univ :=
  isStaticRegularOn_expLapse

example (z : MinkowskiModel (n + 1)) :
    ricciOf (expLapseStatic n).coefficient z 0 0 = Real.exp (2 * z 1) :=
  ricciOf_expLapseStatic_zero_zero z

example {z : MinkowskiModel (n + 1)} (hN : N (spatialPoint z) ≠ 0)
    (hγ : (γ (spatialPoint z)).det ≠ 0) (T : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ) :
    ∑ a, ∑ c, (staticCoefficient N γ z)⁻¹ a c * T a c =
      -T 0 0 / N (spatialPoint z) ^ 2 +
        ∑ α, ∑ β, (γ (spatialPoint z))⁻¹ α β * T α.succ β.succ :=
  staticCoefficient_inv_trace hN hγ T

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {κ : ℝ} {T : MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ} (hE : g.IsEinstein κ 0 T)
    {x : MinkowskiModel 3} (hx : x ∈ U) (i k : Fin 4) :
    ricciOf g.coefficient x i k =
      κ * (T x i k - g.coefficient x i k *
        (∑ a, ∑ c, (g.coefficient x)⁻¹ a c * T x a c) / 2) :=
  IsEinstein.ricciOf_eq hE hx i k

end ProjectAinos.SmoothGeometry.CoordinateMetric

end Static

section NewtonianFieldLimit

open Set Filter TopologicalSpace

open scoped ContDiff Topology Matrix Real

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric

example (ε : ℝ) (Φ : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    ℝ :=
  weakLapse ε Φ x

example (ε : ℝ) (q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  weakSpatial ε q x

example (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    ℝ :=
  flatLaplacian f x

example (ε : ℝ) (q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) (α β : Fin 3) :
    weakSpatial ε q x α β = (1 : Matrix (Fin 3) (Fin 3) ℝ) α β + ε * q x α β :=
  weakSpatial_apply ε q x α β

example {ε : ℝ} {Φ : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hΦ : DifferentiableAt ℝ Φ x)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (weakLapse ε Φ) x v = ε * fderiv ℝ Φ x v :=
  fderiv_weakLapse hΦ v

example {ε : ℝ} {Φ : (Fin 3 → ℝ) → ℝ} {V : Set (Fin 3 → ℝ)} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ V) {x : Fin 3 → ℝ} (hx : x ∈ V) (α β : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (weakLapse ε Φ) y (Pi.single β 1)) x (Pi.single α 1) =
      ε * fderiv ℝ (fun y => fderiv ℝ Φ y (Pi.single β 1)) x (Pi.single α 1) :=
  fderiv_fderiv_weakLapse hV hΦ hx α β

example {ε : ℝ} {q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → ℝ} {α β : Fin 3}
    (hq : DifferentiableAt ℝ (fun y => q y α β) x) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => weakSpatial ε q y α β) x v = ε * fderiv ℝ (fun y => q y α β) x v :=
  fderiv_weakSpatial hq v

example (ε : ℝ) (q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) (μ α β : Fin 3) :
    ℝ :=
  correctionChristoffel ε q x μ α β

example {ε : ℝ} {q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → ℝ}
    (hq : ∀ α β, DifferentiableAt ℝ (fun y => q y α β) x) (μ α β : Fin 3) :
    christoffelOf (weakSpatial ε q) x μ α β = ε * correctionChristoffel ε q x μ α β :=
  christoffelOf_weakSpatial hq μ α β

example {ε : ℝ} {q : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → ℝ}
    (hdet : (weakSpatial ε q x).det ≠ 0) (α β : Fin 3) :
    (weakSpatial ε q x)⁻¹ α β + ε * ∑ μ, (weakSpatial ε q x)⁻¹ α μ * q x μ β =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) α β :=
  inv_weakSpatial_add hdet α β

example {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B :=
  abs_sum_fin_three_le h

example {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B :=
  abs_mul_le_of_le ha hb

example {E : Matrix (Fin 3) (Fin 3) ℝ} (hE : ∀ i j, |E i j| ≤ 1 / 6) :
    (1 + E).det ≠ 0 ∧ ∀ i j, |(1 + E)⁻¹ i j| ≤ 2 :=
  inv_one_add_bound hE

namespace StaticWeakFieldFamily

variable {G : ℝ} {V : Opens (Fin 3 → ℝ)} (f : StaticWeakFieldFamily G V)

example :
    ℝ :=
  smallParameter f

example :
    0 < f.smallParameter :=
  smallParameter_pos f

example {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) :
    ε ∈ Ioc 0 f.maxParameter :=
  mem_Ioc_maxParameter f hε

example {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) :
    ε * f.bound ≤ 1 / 6 :=
  mul_bound_le f hε

example {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    5 / 6 ≤ weakLapse ε (f.potential ε) x ∧ weakLapse ε (f.potential ε) x ≤ 7 / 6 :=
  lapse_mem f hε hx

example {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    (weakSpatial ε (f.spatialCorrection ε) x).det ≠ 0 ∧
      ∀ α β, |(weakSpatial ε (f.spatialCorrection ε) x)⁻¹ α β| ≤ 2 :=
  spatial_inv f hε hx

example {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) :
    IsStaticRegularOn (weakLapse ε (f.potential ε)) (weakSpatial ε (f.spatialCorrection ε)) V :=
  isStaticRegularOn f hε

example (ε : ℝ) (x : Fin 3 → ℝ) :
    ℝ :=
  remainder f ε x

example {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x = ε * f.remainder ε x :=
  flatLaplacian_sub_eq f hε hx

example :
    ℝ :=
  errorConstant f

example (hG : 0 ≤ G) {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    |f.remainder ε x| ≤ f.errorConstant :=
  abs_remainder_le f hG hε hx

example (hG : 0 ≤ G) {ε : ℝ} (hε : ε ∈ Ioc 0 f.smallParameter) {x : Fin 3 → ℝ} (hx : x ∈ V) :
    |flatLaplacian (f.potential ε) x - 4 * π * G * f.density ε x| ≤ f.errorConstant * ε :=
  abs_flatLaplacian_sub_le f hG hε hx

example (hG : 0 ≤ G) {x : Fin 3 → ℝ} (hx : x ∈ V) {Φ ρ : (Fin 3 → ℝ) → ℝ}
    (hΦ : ∀ α, Tendsto (fun ε => fderiv ℝ (fun y => fderiv ℝ (f.potential ε) y (Pi.single α 1))
      x (Pi.single α 1)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ (fun y => fderiv ℝ Φ y (Pi.single α 1)) x (Pi.single α 1))))
    (hρ : Tendsto (fun ε => f.density ε x) (𝓝[>] 0) (𝓝 (ρ x))) :
    flatLaplacian Φ x = 4 * π * G * ρ x :=
  flatLaplacian_eq_of_tendsto f hG hx hΦ hρ

end StaticWeakFieldFamily

example {G : ℝ} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric .timeNegative 3 U}
    {N : (Fin 3 → ℝ) → ℝ} {γ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g.coefficient = staticCoefficient N γ) {T : MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ}
    (hE : g.IsEinstein (8 * π * G) 0 T) {z : MinkowskiModel 3} (hz : z ∈ U)
    (hN : N (spatialPoint z) ≠ 0) (hdet : (γ (spatialPoint z)).det ≠ 0) {ε ρ τ : ℝ}
    (hT : T z 0 0 = ε * ρ * N (spatialPoint z) ^ 2)
    (hτ : ∑ α, ∑ β, (γ (spatialPoint z))⁻¹ α β * T z α.succ β.succ = τ) :
    ricciOf (staticCoefficient N γ) z 0 0 =
      8 * π * G * (ε * ρ * N (spatialPoint z) ^ 2 -
        staticCoefficient N γ z 0 0 * (-(ε * ρ) + τ) / 2) :=
  fieldEquation_of_isEinstein hg hE hz hN hdet hT hτ

namespace StaticWeakFieldFamily

example (G : ℝ) (V : Opens (Fin 3 → ℝ)) :
    StaticWeakFieldFamily G V :=
  trivialFamily G V

example :
    Opens (Fin 3 → ℝ) :=
  openUnitCube

example {x : Fin 3 → ℝ} (hx : x ∈ openUnitCube) :
    |x 0| < 1 :=
  abs_lt_one_of_mem_openUnitCube hx

example (x : Fin 3 → ℝ) :
    ℝ :=
  halfSquarePotential x

example :
    ContDiff ℝ ∞ halfSquarePotential :=
  contDiff_halfSquarePotential

example (y v : Fin 3 → ℝ) :
    fderiv ℝ halfSquarePotential y v = y 0 * v 0 :=
  fderiv_halfSquarePotential y v

example (x : Fin 3 → ℝ) (α β : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ halfSquarePotential y (Pi.single β 1)) x (Pi.single α 1) =
      (Pi.single β (1 : ℝ) : Fin 3 → ℝ) 0 * (Pi.single α (1 : ℝ) : Fin 3 → ℝ) 0 :=
  fderiv_fderiv_halfSquarePotential x α β

example (x : Fin 3 → ℝ) :
    flatLaplacian halfSquarePotential x = 1 :=
  flatLaplacian_halfSquarePotential x

example (G ε : ℝ) (x : Fin 3 → ℝ) :
    ℝ :=
  halfSquareDensity G ε x

example (G : ℝ) (hG : 0 < G) :
    StaticWeakFieldFamily G openUnitCube :=
  halfSquare G hG

example (G : ℝ) (hG : 0 < G) {x : Fin 3 → ℝ} (hx : x ∈ openUnitCube) :
    flatLaplacian halfSquarePotential x = 4 * π * G * (fun _ => 1 / (4 * π * G)) x :=
  halfSquare_poisson G hG hx

end StaticWeakFieldFamily

end ProjectAinos.GeneralRelativity

end NewtonianFieldLimit

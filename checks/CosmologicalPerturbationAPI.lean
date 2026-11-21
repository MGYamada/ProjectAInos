/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.CosmologicalPerturbation

/-! Public consumers of the gravitational stability of an isotropic universe (Landau–Lifshitz §115):
the first-order Ricci tensor of a synchronous perturbation of a flat universe, the linearized
Einstein equations with dust, the scalar modes with the growing and decaying density contrasts and
the fictitious synchronous modes, the tensor modes, and the decay of the vector modes. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section CosmologicalPerturbation

open ContinuousLinearMap Set TopologicalSpace Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation

open SmoothGeometry CoordinateMetric FLRW

local notation "E" => MinkowskiModel 3

namespace Background

example (B : Background) :
    Data :=
  toData B

example (B : Background) :
    B.toData.I = B.I :=
  toData_I B

example (B : Background) :
    B.toData.N = fun _ => 1 :=
  toData_N B

example (B : Background) :
    B.toData.a = B.a :=
  toData_a B

example (B : Background) :
    B.toData.k = 0 :=
  toData_k B

end Background

variable {B : Background} {x z : E}

example :
    z ∈ domain B.toData ↔ z 0 ∈ B.I :=
  mem_domain_iff

example (hz : z ∈ domain B.toData) :
    z 0 ∈ B.I :=
  time_mem_I hz

example (hz : z ∈ domain B.toData) :
    0 < B.a (z 0) :=
  a_pos' hz

example :
    (metric B.toData).IsSynchronous :=
  isSynchronous_background

example :
    (metric B.toData).coefficient z 0 0 = -1 :=
  coefficient_zero_zero

example (α : Fin 3) :
    (metric B.toData).coefficient z 0 α.succ = 0 :=
  coefficient_zero_succ α

example (α : Fin 3) :
    (metric B.toData).coefficient z α.succ 0 = 0 :=
  coefficient_succ_zero α

example (α β : Fin 3) :
    (metric B.toData).coefficient z α.succ β.succ = if α = β then B.a (z 0) ^ 2 else 0 :=
  coefficient_succ_succ α β

example (hz : z ∈ domain B.toData) :
    ((metric B.toData).coefficient z)⁻¹ 0 0 = -1 :=
  inv_zero_zero hz

example (hz : z ∈ domain B.toData) (α : Fin 3) :
    ((metric B.toData).coefficient z)⁻¹ 0 α.succ = 0 :=
  inv_zero_succ hz α

example (hz : z ∈ domain B.toData) (α : Fin 3) :
    ((metric B.toData).coefficient z)⁻¹ α.succ 0 = 0 :=
  inv_succ_zero hz α

example (hz : z ∈ domain B.toData) (α β : Fin 3) :
    ((metric B.toData).coefficient z)⁻¹ α.succ β.succ =
      if α = β then (B.a (z 0) ^ 2)⁻¹ else 0 :=
  inv_succ_succ hz α β

example (hz : z ∈ domain B.toData) (k : Fin 4) :
    christoffelOf (metric B.toData).coefficient z k 0 0 = 0 :=
  bgΓ_zero_zero hz k

example (hz : z ∈ domain B.toData) (j : Fin 4) :
    christoffelOf (metric B.toData).coefficient z 0 0 j = 0 :=
  bgΓ_zero_zero_left hz j

example (hz : z ∈ domain B.toData) (j : Fin 4) :
    christoffelOf (metric B.toData).coefficient z 0 j 0 = 0 :=
  bgΓ_zero_left_zero hz j

example (hz : z ∈ domain B.toData) (α β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z 0 α.succ β.succ =
      if α = β then B.a (z 0) * deriv B.a (z 0) else 0 :=
  bgΓ_zero_succ_succ hz α β

example (hz : z ∈ domain B.toData) (γ β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z γ.succ 0 β.succ =
      if γ = β then deriv B.a (z 0) / B.a (z 0) else 0 :=
  bgΓ_succ_zero_succ hz γ β

example (hz : z ∈ domain B.toData) (γ β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z γ.succ β.succ 0 =
      if γ = β then deriv B.a (z 0) / B.a (z 0) else 0 :=
  bgΓ_succ_succ_zero hz γ β

example (hz : z ∈ domain B.toData) (γ α β : Fin 3) :
    christoffelOf (metric B.toData).coefficient z γ.succ α.succ β.succ = 0 :=
  bgΓ_succ_succ_succ hz γ α β

example {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (z 0)) {f : E → ℝ} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' z) :
    HasFDerivAt (fun w : E => φ (w 0) * f w) (φ (z 0) • f' + f z • (φ' • proj 0)) z :=
  hasFDerivAt_time_mul hφ hf

example {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (z 0)) {f : E → ℝ}
    (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ (fun w : E => φ (w 0) * f w) z v = φ' * v 0 * f z + φ (z 0) * fderiv ℝ f z v :=
  fderiv_time_mul hφ hf v

example {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (z 0)) (v : E) :
    fderiv ℝ (fun w : E => φ (w 0)) z v = φ' * v 0 :=
  fderiv_time hφ v

example {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt B.a (deriv B.a t) t :=
  hasDerivAt_a' ht

example {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt (deriv B.a) (deriv (deriv B.a) t) t :=
  hasDerivAt_deriv_a' ht

example {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt (fun s => B.a s ^ 2) (2 * B.a t * deriv B.a t) t :=
  hasDerivAt_a_sq ht

example {t : ℝ} (ht : t ∈ B.I) :
    HasDerivAt (fun s => B.a s * deriv B.a s)
      (deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t) t :=
  hasDerivAt_a_mul_deriv ht

example (f : Fin 3 → Fin 3 → ℝ) (i j : Fin 4) :
    ℝ :=
  spatialBlock f i j

example (f : Fin 3 → Fin 3 → ℝ) (j : Fin 4) :
    spatialBlock f 0 j = 0 :=
  spatialBlock_zero_left f j

example (f : Fin 3 → Fin 3 → ℝ) (i : Fin 4) :
    spatialBlock f i 0 = 0 :=
  spatialBlock_zero_right f i

example (f : Fin 3 → Fin 3 → ℝ) (α β : Fin 3) :
    spatialBlock f α.succ β.succ = f α β :=
  spatialBlock_succ_succ f α β

example (h : E → Fin 3 → Fin 3 → ℝ) (c : Fin 4) (z : E) (α β : Fin 3) :
    ℝ :=
  dh h c z α β

example (h : E → Fin 3 → Fin 3 → ℝ) (c e : Fin 4) (z : E) (α β : Fin 3) :
    ℝ :=
  ddh h c e z α β

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  metricPerturbation B h z

example (h : E → Fin 3 → Fin 3 → ℝ) (ε : ℝ) (z : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  perturbedCoefficient B h ε z

example (h : E → Fin 3 → Fin 3 → ℝ) (ε : ℝ) (z : E) :
    perturbedCoefficient B h ε z 0 0 = -1 ∧
      (∀ α : Fin 3, perturbedCoefficient B h ε z 0 α.succ = 0) ∧
      ∀ α β : Fin 3, perturbedCoefficient B h ε z α.succ β.succ =
        B.a (z 0) ^ 2 * ((if α = β then 1 else 0) + ε * h z α β) :=
  perturbedCoefficient_synchronous h ε z

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (j : Fin 4) :
    metricPerturbation B h z 0 j = 0 :=
  metricPerturbation_zero_left h z j

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (i : Fin 4) :
    metricPerturbation B h z i 0 = 0 :=
  metricPerturbation_zero_right h z i

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (α β : Fin 3) :
    metricPerturbation B h z α.succ β.succ = B.a (z 0) ^ 2 * h z α β :=
  metricPerturbation_succ_succ h z α β

example (h : E → Fin 3 → Fin 3 → ℝ) (j : Fin 4) (v : E) :
    fderiv ℝ (fun w => metricPerturbation B h w 0 j) z v = 0 :=
  fderiv_metricPerturbation_zero_left h j v

example (h : E → Fin 3 → Fin 3 → ℝ) (i : Fin 4) (v : E) :
    fderiv ℝ (fun w => metricPerturbation B h w i 0) z v = 0 :=
  fderiv_metricPerturbation_zero_right h i v

example {h : E → Fin 3 → Fin 3 → ℝ} (hz : z ∈ domain B.toData) {α β : Fin 3}
    (hh : DifferentiableAt ℝ (fun w => h w α β) z) (v : E) :
    fderiv ℝ (fun w => metricPerturbation B h w α.succ β.succ) z v =
      2 * B.a (z 0) * deriv B.a (z 0) * v 0 * h z α β +
        B.a (z 0) ^ 2 * fderiv ℝ (fun w => h w α β) z v :=
  fderiv_metricPerturbation_succ_succ hz hh v

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (hz : z ∈ domain B.toData)
    (α β : Fin 3) :
    DifferentiableAt ℝ (fun w => h w α β) z :=
  IsPerturbation.differentiableAt hP hz α β

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (c : Fin 4) (z : E) (α β : Fin 3) :
    dh h c z α β = dh h c z β α :=
  IsPerturbation.dh_symm hP c z α β

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (c e : Fin 4) (z : E) (α β : Fin 3) :
    ddh h c e z α β = ddh h c e z β α :=
  IsPerturbation.ddh_symm hP c e z α β

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => metricPerturbation B h z i j) (domain B.toData) :=
  IsPerturbation.contDiffOn_metricPerturbation hP i j

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (z : E) (i j : Fin 4) :
    metricPerturbation B h z i j = metricPerturbation B h z j i :=
  IsPerturbation.metricPerturbation_symm hP z i j

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (k i j : Fin 4) :
    ℝ :=
  linChristoffel B h z k i j

section linChristoffel

variable (h : E → Fin 3 → Fin 3 → ℝ) (z : E)

example (j : Fin 4) :
    linChristoffel B h z 0 0 j = 0 :=
  linChristoffel_zero_zero h z j

example (α : Fin 3) :
    linChristoffel B h z 0 α.succ 0 = 0 :=
  linChristoffel_zero_succ_zero h z α

example (α β : Fin 3) :
    linChristoffel B h z 0 α.succ β.succ =
      B.a (z 0) * deriv B.a (z 0) * h z α β + B.a (z 0) ^ 2 * dh h 0 z α β / 2 :=
  linChristoffel_zero_succ_succ h z α β

example (γ : Fin 3) :
    linChristoffel B h z γ.succ 0 0 = 0 :=
  linChristoffel_succ_zero_zero h z γ

example (γ β : Fin 3) :
    linChristoffel B h z γ.succ 0 β.succ = dh h 0 z γ β / 2 :=
  linChristoffel_succ_zero_succ h z γ β

example (γ α : Fin 3) :
    linChristoffel B h z γ.succ α.succ 0 = dh h 0 z γ α / 2 :=
  linChristoffel_succ_succ_zero h z γ α

example (γ α β : Fin 3) :
    linChristoffel B h z γ.succ α.succ β.succ =
      (dh h α.succ z γ β + dh h β.succ z γ α - dh h γ.succ z α β) / 2 :=
  linChristoffel_succ_succ_succ h z γ α β

end linChristoffel

example :
    (Pi.single 0 1 : E) 0 = 1 :=
  single_zero_apply_zero

example (α : Fin 3) :
    (Pi.single α.succ 1 : E) 0 = 0 :=
  single_succ_apply_zero α

example {h : E → Fin 3 → Fin 3 → ℝ} (hz : z ∈ domain B.toData) {α β : Fin 3}
    (hh : DifferentiableAt ℝ (fun w => h w α β) z) (c : Fin 4) :
    fderiv ℝ (fun w => metricPerturbation B h w α.succ β.succ) z (Pi.single c 1) =
      2 * B.a (z 0) * deriv B.a (z 0) * (Pi.single c 1 : E) 0 * h z α β +
        B.a (z 0) ^ 2 * dh h c z α β :=
  fderiv_metricPerturbation_single hz hh c

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (hz : z ∈ domain B.toData)
    (k i j : Fin 4) :
    (metric B.toData).curvedChristoffel (metricPerturbation B h) z k i j =
      linChristoffel B h z k i j :=
  curvedChristoffel_eq hP hz k i j

section Ricci

variable {h : E → Fin 3 → Fin 3 → ℝ}

example (hP : IsPerturbation B h) (c : Fin 4) (α β : Fin 3) :
    ContDiffOn ℝ ∞ (fun w => dh h c w α β) (domain B.toData) :=
  IsPerturbation.contDiffOn_dh hP c α β

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (c : Fin 4) (α β : Fin 3) :
    DifferentiableAt ℝ (fun w => dh h c w α β) x :=
  IsPerturbation.differentiableAt_dh hP hx c α β

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (a b : Fin 4) (α β : Fin 3) :
    ddh h a b x α β = ddh h b a x α β :=
  IsPerturbation.ddh_comm hP hx a b α β

example :
    ℝ × E → Matrix (Fin 4) (Fin 4) ℝ :=
  family B h

example (hP : IsPerturbation B h) (hz : z ∈ domain B.toData) (k i j : Fin 4) :
    familyChristoffelDeriv (family B h) z k i j = linChristoffel B h z k i j :=
  familyChristoffelDeriv_eq_lin hP hz k i j

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (j k : Fin 4) :
    HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x j k)
      (familyRicciDeriv (family B h) x j k) 0 :=
  hasDerivAt_ricciOf_family hP hx j k

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (j k : Fin 4) :
    familyRicciDeriv (family B h) x j k =
      ∑ i, (fderiv ℝ (fun z => linChristoffel B h z i j k) x (Pi.single i 1) -
        fderiv ℝ (fun z => linChristoffel B h z i i k) x (Pi.single j 1) +
        ∑ a, ((linChristoffel B h x i i a * christoffelOf (metric B.toData).coefficient x a j k +
            christoffelOf (metric B.toData).coefficient x i i a * linChristoffel B h x a j k) -
          (linChristoffel B h x i j a * christoffelOf (metric B.toData).coefficient x a i k +
            christoffelOf (metric B.toData).coefficient x i j a *
              linChristoffel B h x a i k))) :=
  familyRicciDeriv_eq_lin hP hx j k

example {f : E → ℝ} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun z => f z / 2) x :=
  differentiableAt_div_two hf

example {f : E → ℝ} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun z => f z / 2) x v = fderiv ℝ f x v / 2 :=
  fderiv_div_two hf v

example (j : Fin 4) (v : E) :
    fderiv ℝ (fun z => linChristoffel B h z 0 0 j) x v = 0 :=
  fderiv_lin_zero_zero j v

example (α : Fin 3) (v : E) :
    fderiv ℝ (fun z => linChristoffel B h z 0 α.succ 0) x v = 0 :=
  fderiv_lin_zero_succ_zero α v

example (γ : Fin 3) (v : E) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ 0 0) x v = 0 :=
  fderiv_lin_succ_zero_zero γ v

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (α β : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z 0 α.succ β.succ) x (Pi.single c 1) =
      (deriv B.a (x 0) ^ 2 + B.a (x 0) * deriv (deriv B.a) (x 0)) * (Pi.single c 1 : E) 0 *
          h x α β + B.a (x 0) * deriv B.a (x 0) * dh h c x α β +
        B.a (x 0) * deriv B.a (x 0) * (Pi.single c 1 : E) 0 * dh h 0 x α β +
        B.a (x 0) ^ 2 / 2 * ddh h c 0 x α β :=
  fderiv_lin_zero_succ_succ hP hx α β c

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (γ β : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ 0 β.succ) x (Pi.single c 1) =
      ddh h c 0 x γ β / 2 :=
  fderiv_lin_succ_zero_succ hP hx γ β c

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (γ α : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ α.succ 0) x (Pi.single c 1) =
      ddh h c 0 x γ α / 2 :=
  fderiv_lin_succ_succ_zero hP hx γ α c

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (γ α β : Fin 3) (c : Fin 4) :
    fderiv ℝ (fun z => linChristoffel B h z γ.succ α.succ β.succ) x (Pi.single c 1) =
      (ddh h c α.succ x γ β + ddh h c β.succ x γ α - ddh h c γ.succ x α β) / 2 :=
  fderiv_lin_succ_succ_succ hP hx γ α β c

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) :
    ℝ :=
  linRicciTime B h z

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (α : Fin 3) :
    ℝ :=
  linRicciMixed h z α

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (α β : Fin 3) :
    ℝ :=
  linRicciSpace B h z α β

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) :
    familyRicciDeriv (family B h) x 0 0 = linRicciTime B h x :=
  familyRicciDeriv_zero_zero hP hx

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (β : Fin 3) :
    familyRicciDeriv (family B h) x 0 β.succ = linRicciMixed h x β :=
  familyRicciDeriv_zero_succ hP hx β

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (α : Fin 3) :
    familyRicciDeriv (family B h) x α.succ 0 = linRicciMixed h x α :=
  familyRicciDeriv_succ_zero hP hx α

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (α β : Fin 3) :
    familyRicciDeriv (family B h) x α.succ β.succ = linRicciSpace B h x α β :=
  familyRicciDeriv_succ_succ hP hx α β

example (h : E → Fin 3 → Fin 3 → ℝ) (z : E) (j k : Fin 4) :
    ℝ :=
  linRicci B h z j k

example (z : E) :
    linRicci B h z 0 0 = linRicciTime B h z :=
  linRicci_zero_zero z

example (z : E) (β : Fin 3) :
    linRicci B h z 0 β.succ = linRicciMixed h z β :=
  linRicci_zero_succ z β

example (z : E) (α : Fin 3) :
    linRicci B h z α.succ 0 = linRicciMixed h z α :=
  linRicci_succ_zero z α

example (z : E) (α β : Fin 3) :
    linRicci B h z α.succ β.succ = linRicciSpace B h z α β :=
  linRicci_succ_succ z α β

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (j k : Fin 4) :
    familyRicciDeriv (family B h) x j k = linRicci B h x j k :=
  familyRicciDeriv_eq_linRicci hP hx j k

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) (j k : Fin 4) :
    HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x j k) (linRicci B h x j k) 0 :=
  hasDerivAt_ricciOf_perturbed hP hx j k

example (hP : IsPerturbation B h) (hx : x ∈ domain B.toData) :
    HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x 0 0)
        (-(∑ γ, ddh h 0 0 x γ γ) / 2 - deriv B.a (x 0) / B.a (x 0) * ∑ γ, dh h 0 x γ γ) 0 ∧
      (∀ α : Fin 3, HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x 0 α.succ)
        ((∑ γ, ddh h γ.succ 0 x γ α - ∑ γ, ddh h 0 α.succ x γ γ) / 2) 0) ∧
      (∀ α : Fin 3, HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x α.succ 0)
        ((∑ γ, ddh h γ.succ 0 x γ α - ∑ γ, ddh h 0 α.succ x γ γ) / 2) 0) ∧
      ∀ α β : Fin 3, HasDerivAt (fun ε => ricciOf (perturbedCoefficient B h ε) x α.succ β.succ)
        ((∑ γ, (ddh h γ.succ α.succ x γ β + ddh h γ.succ β.succ x γ α -
              ddh h γ.succ γ.succ x α β) - ∑ γ, ddh h α.succ β.succ x γ γ) / 2 +
          (2 * deriv B.a (x 0) ^ 2 + B.a (x 0) * deriv (deriv B.a) (x 0)) * h x α β +
          3 / 2 * (B.a (x 0) * deriv B.a (x 0)) * dh h 0 x α β +
          B.a (x 0) ^ 2 / 2 * ddh h 0 0 x α β +
          if α = β then B.a (x 0) * deriv B.a (x 0) / 2 * ∑ γ, dh h 0 x γ γ else 0) 0 :=
  ricci_synchronous_deriv hP hx

end Ricci

section Dust

variable {κ : ℝ} {ρ : ℝ → ℝ}

example (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0)) {t : ℝ}
    (ht : t ∈ B.I) :
    deriv B.a t ^ 2 = κ * ρ t * B.a t ^ 2 / 3 ∧
      B.a t * deriv (deriv B.a) t = -(κ * ρ t * B.a t ^ 2) / 6 :=
  dust_background hB ht

example (v : E → Fin 3 → ℝ) (ε : ℝ) (z : E) :
    Fin 4 → ℝ :=
  velocity v ε z

example (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (ε : ℝ) (z : E)
    (i k : Fin 4) :
    ℝ :=
  dustSource B ρ h δ v ε z i k

example (κ : ℝ) (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (ε : ℝ)
    (z : E) (i k : Fin 4) :
    ℝ :=
  dustResidual B κ ρ h δ v ε z i k

example (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E)
    (i k : Fin 4) :
    ℝ :=
  linDust B ρ h δ v z i k

section linDust

variable (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E)

example :
    linDust B ρ h δ v z 0 0 = ρ (z 0) * δ z / 2 :=
  linDust_zero_zero h δ v z

example (β : Fin 3) :
    linDust B ρ h δ v z 0 β.succ = -(ρ (z 0) * v z β) :=
  linDust_zero_succ h δ v z β

example (α : Fin 3) :
    linDust B ρ h δ v z α.succ 0 = -(ρ (z 0) * v z α) :=
  linDust_succ_zero h δ v z α

example (α β : Fin 3) :
    linDust B ρ h δ v z α.succ β.succ =
      ρ (z 0) * B.a (z 0) ^ 2 * ((if α = β then δ z else 0) + h z α β) / 2 :=
  linDust_succ_succ h δ v z α β

end linDust

example (v : E → Fin 3 → ℝ) (z : E) (i : Fin 4) :
    HasDerivAt (fun ε => velocity v ε z i)
      (Fin.cons (α := fun _ => ℝ) 0 (fun α => v z α) i) 0 :=
  hasDerivAt_velocity v z i

example (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E) (i k : Fin 4) :
    HasDerivAt (fun ε => dustSource B ρ h δ v ε z i k) (linDust B ρ h δ v z i k) 0 :=
  hasDerivAt_dustSource h δ v z i k

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (δ : E → ℝ) (v : E → Fin 3 → ℝ)
    (hx : x ∈ domain B.toData) (i k : Fin 4) :
    HasDerivAt (fun ε => dustResidual B κ ρ h δ v ε x i k)
      (linRicci B h x i k - κ * linDust B ρ h δ v x i k) 0 :=
  hasDerivAt_dustResidual hP δ v hx i k

example (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0))
    (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (hx : x ∈ domain B.toData)
    (i k : Fin 4) :
    dustResidual B κ ρ h δ v 0 x i k = 0 :=
  dustResidual_zero hB h δ v hx i k

example (κ : ℝ) (ρ : ℝ → ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) :
    Prop :=
  LinearizedEinsteinDust B κ ρ h δ v

example {h : E → Fin 3 → Fin 3 → ℝ} (hP : IsPerturbation B h) (δ : E → ℝ) (v : E → Fin 3 → ℝ) :
    LinearizedEinsteinDust B κ ρ h δ v ↔
      ∀ x ∈ domain B.toData, ∀ i k, deriv (fun ε => dustResidual B κ ρ h δ v ε x i k) 0 = 0 :=
  linearizedEinsteinDust_iff_deriv hP δ v

end Dust

section Wave

example (n : Fin 3 → ℝ) :
    E →L[ℝ] ℝ :=
  phaseCLM n

example (n : Fin 3 → ℝ) (z : E) :
    ℝ :=
  phase n z

example (n : Fin 3 → ℝ) (z : E) :
    phaseCLM n z = phase n z :=
  phaseCLM_apply n z

example (n : Fin 3 → ℝ) :
    ℝ :=
  nsq n

example {n : Fin 3 → ℝ} (hn : n ≠ 0) :
    nsq n ≠ 0 :=
  nsq_ne_zero hn

example (n : Fin 3 → ℝ) (z : E) :
    HasFDerivAt (phase n) (phaseCLM n) z :=
  hasFDerivAt_phase n z

example (n : Fin 3 → ℝ) :
    phaseCLM n (Pi.single 0 1) = 0 :=
  phaseCLM_single_zero n

example (n : Fin 3 → ℝ) (δ : Fin 3) :
    phaseCLM n (Pi.single δ.succ 1) = n δ :=
  phaseCLM_single_succ n δ

example (n : Fin 3 → ℝ) (t s : ℝ) :
    E :=
  wavePoint n t s

example (n : Fin 3 → ℝ) (t s : ℝ) :
    wavePoint n t s 0 = t :=
  wavePoint_zero n t s

example {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) (t s : ℝ) :
    phase n (wavePoint n t s) = s :=
  phase_wavePoint hn t s

example {n : Fin 3 → ℝ} {t : ℝ} (ht : t ∈ B.I) (s : ℝ) :
    wavePoint n t s ∈ domain B.toData :=
  wavePoint_mem ht s

example {n : Fin 3 → ℝ} {f k : ℝ → ℝ} {f' k' : ℝ} (hf : HasDerivAt f f' (z 0))
    (hk : HasDerivAt k k' (phase n z)) (v : E) :
    fderiv ℝ (fun w => f (w 0) * k (phase n w)) z v =
      f' * v 0 * k (phase n z) + f (z 0) * k' * phaseCLM n v :=
  fderiv_wave hf hk v

example {n : Fin 3 → ℝ} {f k : ℝ → ℝ} {f' k' : ℝ} (hf : HasDerivAt f f' (z 0))
    (hk : HasDerivAt k k' (phase n z)) :
    DifferentiableAt ℝ (fun w => f (w 0) * k (phase n w)) z :=
  differentiableAt_wave hf hk

example (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) :
    ℝ :=
  Fd F t α β

example (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) :
    ℝ :=
  Fdd F t α β

example (F : ℝ → Fin 3 → Fin 3 → ℝ) (k : ℝ → ℝ) (n : Fin 3 → ℝ) (z : E) (α β : Fin 3) :
    ℝ :=
  mode F k n z α β

example :
    IsProfile Real.cos fun s => -Real.sin s :=
  isProfile_cos

example :
    IsProfile Real.sin Real.cos :=
  isProfile_sin

variable {F : ℝ → Fin 3 → Fin 3 → ℝ} {k k₁ : ℝ → ℝ} {n : Fin 3 → ℝ}

example (hF : IsAmplitude B F) {t : ℝ} (ht : t ∈ B.I) (α β : Fin 3) :
    HasDerivAt (fun s => F s α β) (Fd F t α β) t :=
  IsAmplitude.hasDerivAt hF ht α β

example (hF : IsAmplitude B F) {t : ℝ} (ht : t ∈ B.I) (α β : Fin 3) :
    HasDerivAt (fun s => Fd F s α β) (Fdd F t α β) t :=
  IsAmplitude.hasDerivAt_Fd hF ht α β

example (hF : IsAmplitude B F) (hk : IsProfile k k₁) :
    IsPerturbation B (mode F k n) :=
  IsAmplitude.isPerturbation hF hk

example (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hz : z ∈ domain B.toData) (c : Fin 4)
    (α β : Fin 3) :
    dh (mode F k n) c z α β =
      Fd F (z 0) α β * (Pi.single c 1 : E) 0 * k (phase n z) +
        F (z 0) α β * phaseCLM n (Pi.single c 1) * k₁ (phase n z) :=
  dh_mode hF hk hz c α β

example (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hx : x ∈ domain B.toData) (c' c : Fin 4)
    (α β : Fin 3) :
    ddh (mode F k n) c' c x α β =
      (Pi.single c 1 : E) 0 * (Pi.single c' 1 : E) 0 * Fdd F (x 0) α β * k (phase n x) +
        ((Pi.single c 1 : E) 0 * phaseCLM n (Pi.single c' 1) +
          phaseCLM n (Pi.single c 1) * (Pi.single c' 1 : E) 0) * Fd F (x 0) α β *
            k₁ (phase n x) -
        phaseCLM n (Pi.single c 1) * phaseCLM n (Pi.single c' 1) * F (x 0) α β *
          k (phase n x) :=
  ddh_mode hF hk hx c' c α β

example (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) :
    ℝ :=
  modeTime B F t

example (F : ℝ → Fin 3 → Fin 3 → ℝ) (n : Fin 3 → ℝ) (t : ℝ) (α : Fin 3) :
    ℝ :=
  modeMixed F n t α

example (F : ℝ → Fin 3 → Fin 3 → ℝ) (n : Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) :
    ℝ :=
  modeSpace B F n t α β

example (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hx : x ∈ domain B.toData) :
    linRicciTime B (mode F k n) x = modeTime B F (x 0) * k (phase n x) :=
  linRicciTime_mode hF hk hx

example (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hx : x ∈ domain B.toData) (α : Fin 3) :
    linRicciMixed (mode F k n) x α = modeMixed F n (x 0) α * k₁ (phase n x) :=
  linRicciMixed_mode hF hk hx α

example (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hx : x ∈ domain B.toData) (α β : Fin 3) :
    linRicciSpace B (mode F k n) x α β = modeSpace B F n (x 0) α β * k (phase n x) :=
  linRicciSpace_mode hF hk hx α β

example {κ : ℝ} {ρ : ℝ → ℝ} (hF : IsAmplitude B F) (hk : IsProfile k k₁) (hn : nsq n ≠ 0)
    (hk0 : ∃ s, k s ≠ 0) (hk1 : ∃ s, k₁ s ≠ 0) (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ) :
    LinearizedEinsteinDust B κ ρ (mode F k n) (fun z => dc (z 0) * k (phase n z))
        (fun z α => V (z 0) α * k₁ (phase n z)) ↔
      ∀ t ∈ B.I, modeTime B F t = κ * (ρ t * dc t / 2) ∧
        (∀ α, modeMixed F n t α = κ * -(ρ t * V t α)) ∧
        ∀ α β, modeSpace B F n t α β =
          κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + F t α β) / 2) :=
  mode_iff hF hk hn hk0 hk1 dc V

end Wave

section Scalar

example (α β : Fin 3) :
    ℝ :=
  kron α β

example (n : Fin 3 → ℝ) (α β : Fin 3) :
    ℝ :=
  longitudinal n α β

example (f : Fin 3 → ℝ) (β : Fin 3) :
    ∑ γ, f γ * kron γ β = f β :=
  sum_kron_mul f β

example :
    ∑ γ : Fin 3, kron γ γ = 3 :=
  sum_kron_diag

example {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) :
    ∑ γ, longitudinal n γ γ = 0 :=
  sum_longitudinal_diag hn

example {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) (β : Fin 3) :
    ∑ γ, n γ * longitudinal n γ β = 2 / 3 * n β :=
  sum_mul_longitudinal hn β

example (n : Fin 3 → ℝ) (α β : Fin 3) :
    longitudinal n α β = longitudinal n β α :=
  longitudinal_symm n α β

example (α β : Fin 3) :
    kron α β = kron β α :=
  kron_symm α β

example {n : Fin 3 → ℝ} (hn : nsq n ≠ 0) (A C : ℝ) :
    (∀ α β, A * longitudinal n α β + C * (kron α β / 3) = 0) ↔ A = 0 ∧ C = 0 :=
  scalar_decomp_eq_zero_iff hn A C

example (n : Fin 3 → ℝ) (lam mu : ℝ → ℝ) (t : ℝ) (α β : Fin 3) :
    ℝ :=
  scalarAmp n lam mu t α β

example (n : Fin 3 → ℝ) (lam mu : ℝ → ℝ) :
    E → Fin 3 → Fin 3 → ℝ :=
  scalarMode n lam mu

example (n : Fin 3 → ℝ) (lam mu : ℝ → ℝ) (z : E) (α β : Fin 3) :
    scalarMode n lam mu z α β =
      lam (z 0) * (n α * n β / nsq n - (if α = β then 1 else 0) / 3) * Real.cos (phase n z) +
        mu (z 0) * ((if α = β then 1 else 0) / 3) * Real.cos (phase n z) :=
  scalarMode_apply n lam mu z α β

variable {lam mu : ℝ → ℝ} {n : Fin 3 → ℝ}

example (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) :
    IsAmplitude B (scalarAmp n lam mu) :=
  isAmplitude_scalarAmp hlam hmu

example (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) :
    IsPerturbation B (scalarMode n lam mu) :=
  isPerturbation_scalarMode hlam hmu

example (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) {t : ℝ} (ht : t ∈ B.I)
    (α β : Fin 3) :
    Fd (scalarAmp n lam mu) t α β = scalarAmp n (deriv lam) (deriv mu) t α β :=
  Fd_scalarAmp hlam hmu ht α β

example (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) {t : ℝ} (ht : t ∈ B.I)
    (α β : Fin 3) :
    Fdd (scalarAmp n lam mu) t α β =
      scalarAmp n (deriv (deriv lam)) (deriv (deriv mu)) t α β :=
  Fdd_scalarAmp hlam hmu ht α β

example (hn : nsq n ≠ 0) (lam mu : ℝ → ℝ) (t : ℝ) :
    ∑ γ, scalarAmp n lam mu t γ γ = mu t :=
  sum_scalarAmp_diag hn lam mu t

example (hn : nsq n ≠ 0) (lam mu : ℝ → ℝ) (t : ℝ) (β : Fin 3) :
    ∑ γ, n γ * scalarAmp n lam mu t γ β = (2 / 3 * lam t + mu t / 3) * n β :=
  sum_mul_scalarAmp hn lam mu t β

example (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) (hn : nsq n ≠ 0) {t : ℝ}
    (ht : t ∈ B.I) :
    modeTime B (scalarAmp n lam mu) t =
      -deriv (deriv mu) t / 2 - deriv B.a t / B.a t * deriv mu t :=
  modeTime_scalarAmp hlam hmu hn ht

example (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) (hn : nsq n ≠ 0) {t : ℝ}
    (ht : t ∈ B.I) (α : Fin 3) :
    modeMixed (scalarAmp n lam mu) n t α = (deriv lam t - deriv mu t) * n α / 3 :=
  modeMixed_scalarAmp hlam hmu hn ht α

example {κ : ℝ} {ρ : ℝ → ℝ} (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I)
    (hn : nsq n ≠ 0) {t : ℝ} (ht : t ∈ B.I)
    (hbg : 2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t = κ * ρ t * B.a t ^ 2 / 2)
    (dc : ℝ → ℝ) (α β : Fin 3) :
    modeSpace B (scalarAmp n lam mu) n t α β -
        κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + scalarAmp n lam mu t α β) / 2) =
      B.a t ^ 2 / 2 * (deriv (deriv lam) t + 3 * (deriv B.a t / B.a t) * deriv lam t +
          nsq n * (mu t - lam t) / (3 * B.a t ^ 2)) * longitudinal n α β +
        B.a t ^ 2 / 2 * (deriv (deriv mu) t + 6 * (deriv B.a t / B.a t) * deriv mu t +
          4 * nsq n * (mu t - lam t) / (3 * B.a t ^ 2) - 3 * κ * ρ t * dc t) *
          (kron α β / 3) :=
  modeSpace_scalarAmp hlam hmu hn ht hbg dc α β

example {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0))
    (hn : n ≠ 0) (hlam : ContDiffOn ℝ ∞ lam B.I) (hmu : ContDiffOn ℝ ∞ mu B.I) (dc w : ℝ → ℝ) :
    LinearizedEinsteinDust B κ ρ (scalarMode n lam mu) (fun z => dc (z 0) * Real.cos (phase n z))
        (fun z α => w (z 0) * n α * Real.sin (phase n z)) ↔
      ∀ t ∈ B.I,
        deriv (deriv lam) t + 3 * (deriv B.a t / B.a t) * deriv lam t +
            nsq n * (mu t - lam t) / (3 * B.a t ^ 2) = 0 ∧
        deriv (deriv mu) t + 3 * (deriv B.a t / B.a t) * deriv mu t +
            nsq n * (mu t - lam t) / (3 * B.a t ^ 2) = 0 ∧
        κ * ρ t * dc t = -(deriv (deriv mu) t + 2 * (deriv B.a t / B.a t) * deriv mu t) ∧
        deriv mu t - deriv lam t = -(3 * κ * ρ t * w t) :=
  scalarMode_iff hB hn hlam hmu dc w

end Scalar

section DustUniverse

example {t : ℝ} (ht : 0 < t) (k : ℤ) :
    t ^ ((k : ℝ) / 3) = (t ^ (1 / 3 : ℝ)) ^ k :=
  rpow_div_three ht k

example {t : ℝ} (ht : 0 < t) :
    0 < t ^ (1 / 3 : ℝ) :=
  cbrt_pos ht

example {t : ℝ} (ht : 0 < t) :
    (t ^ (1 / 3 : ℝ)) ^ 3 = t :=
  cbrt_cube ht

example (A K : ℝ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => A * s ^ ((k : ℝ) / 3) + K)
      (A * ((k : ℝ) / 3) * t ^ (((k - 3 : ℤ) : ℝ) / 3)) t :=
  hasDerivAt_powThird A K k ht

example (A K : ℝ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => A * s ^ ((k : ℝ) / 3) + K) t =
      A * ((k : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 3) :=
  deriv_powThird A K k ht

example (A K : ℝ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv fun s => A * s ^ ((k : ℝ) / 3) + K) t =
      A * ((k : ℝ) / 3) * (((k - 3 : ℤ) : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 6) :=
  deriv_deriv_powThird A K k ht

example (A K q : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => A * s ^ q + K) (Ioi 0) :=
  contDiffOn_powThird A K q

example (A C : ℝ) (k m : ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3))
      (A * ((k : ℝ) / 3) * t ^ (((k - 3 : ℤ) : ℝ) / 3) +
        C * ((m : ℝ) / 3) * t ^ (((m - 3 : ℤ) : ℝ) / 3)) t :=
  hasDerivAt_powPair A C k m ht

example (A C : ℝ) (k m : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3)) t =
      A * ((k : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 3) +
        C * ((m : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (m - 3) :=
  deriv_powPair A C k m ht

example (A C : ℝ) (k m : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv fun s => A * s ^ ((k : ℝ) / 3) + C * s ^ ((m : ℝ) / 3)) t =
      A * ((k : ℝ) / 3) * (((k - 3 : ℤ) : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (k - 6) +
        C * ((m : ℝ) / 3) * (((m - 3 : ℤ) : ℝ) / 3) * (t ^ (1 / 3 : ℝ)) ^ (m - 6) :=
  deriv_deriv_powPair A C k m ht

example (A C q r : ℝ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => A * s ^ q + C * s ^ r) (Ioi 0) :=
  contDiffOn_powPair A C q r

example :
    Background :=
  dustBackground

example (κ t : ℝ) :
    ℝ :=
  dustDensity κ t

example :
    dustBackground.a = fun s => 1 * s ^ (((2 : ℤ) : ℝ) / 3) + 0 :=
  dustBackground_a_eq

example {t : ℝ} (ht : 0 < t) :
    dustBackground.a t = (t ^ (1 / 3 : ℝ)) ^ 2 :=
  dustBackground_a ht

example {t : ℝ} (ht : 0 < t) :
    deriv dustBackground.a t = 2 / 3 * (t ^ (1 / 3 : ℝ)) ^ (-1 : ℤ) :=
  deriv_dustBackground_a ht

example {t : ℝ} (ht : 0 < t) :
    deriv (deriv dustBackground.a) t = -(2 / 9) * (t ^ (1 / 3 : ℝ)) ^ (-4 : ℤ) :=
  deriv_deriv_dustBackground_a ht

example {κ : ℝ} (hκ : κ ≠ 0) :
    (metric dustBackground.toData).IsEinstein κ 0
      (perfectFluidStress dustBackground.toData (dustDensity κ) fun _ => 0) :=
  isEinstein_dustBackground hκ

example {κ : ℝ} (hκ : κ ≠ 0) {n : Fin 3 → ℝ} (hn : n ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (scalarMode n (fun t => -2 * c * t ^ (2 / 3 : ℝ) - 20 * c / (3 * nsq n))
        (fun t => -2 * c * t ^ (2 / 3 : ℝ)))
      (fun z => c * z 0 ^ (2 / 3 : ℝ) * Real.cos (phase n z)) fun _ _ => 0 :=
  densityContrast_growing hκ hn c

example {κ : ℝ} (hκ : κ ≠ 0) {n : Fin 3 → ℝ} (hn : n ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (scalarMode n (fun t => -2 * c * t ^ (-1 : ℝ)) (fun t => -2 * c * t ^ (-1 : ℝ)))
      (fun z => c * z 0 ^ (-1 : ℝ) * Real.cos (phase n z)) fun _ _ => 0 :=
  densityContrast_decaying hκ hn c

end DustUniverse

section Gauge

variable {P : ℝ → ℝ} {F : ℝ} {n : Fin 3 → ℝ}

example (P : ℝ → ℝ) (F : ℝ) (n : Fin 3 → ℝ) (z : E) :
    E :=
  gaugeField P F n z

example :
    (fun w => gaugeField P F n w 0) = fun w => (fun _ : ℝ => F) (w 0) * Real.cos (phase n w) :=
  gaugeField_zero

example (γ : Fin 3) :
    (fun w => gaugeField P F n w γ.succ) =
      fun w => (fun t => -F * n γ * P t) (w 0) * Real.sin (phase n w) :=
  gaugeField_succ γ

example (z v : E) :
    fderiv ℝ (fun w => gaugeField P F n w 0) z v =
      -(F * Real.sin (phase n z) * phaseCLM n v) :=
  fderiv_gaugeField_zero z v

example {P' : ℝ} (hP : HasDerivAt P P' (z 0)) (γ : Fin 3) (v : E) :
    fderiv ℝ (fun w => gaugeField P F n w γ.succ) z v =
      -(F * n γ * (P' * v 0 * Real.sin (phase n z) +
        P (z 0) * Real.cos (phase n z) * phaseCLM n v)) :=
  fderiv_gaugeField_succ hP γ v

example (hz : z ∈ domain B.toData) (α β : Fin 3) (v : E) :
    fderiv ℝ (fun w => (metric B.toData).coefficient w α.succ β.succ) z v =
      if α = β then 2 * B.a (z 0) * deriv B.a (z 0) * v 0 else 0 :=
  fderiv_coefficient_succ_succ hz α β v

example (i : Fin 4) (v : E) :
    fderiv ℝ (fun w => (metric B.toData).coefficient w 0 i) z v = 0 :=
  fderiv_coefficient_zero_left i v

example (i : Fin 4) (v : E) :
    fderiv ℝ (fun w => (metric B.toData).coefficient w i 0) z v = 0 :=
  fderiv_coefficient_zero_right i v

example (hP : ∀ t ∈ B.I, HasDerivAt P (B.a t ^ 2)⁻¹ t) (hn : nsq n ≠ 0) (hz : z ∈ domain B.toData) :
    coordinateLieMetric (gaugeField P F n) (metric B.toData) z =
      metricPerturbation B (scalarMode n (fun t => -2 * F * nsq n * P t)
        (fun t => -2 * F * nsq n * P t + 6 * F * (deriv B.a t / B.a t))) z :=
  coordinateLieMetric_gaugeField hP hn hz

example (hP : ContDiffOn ℝ ∞ P B.I) :
    ContDiffOn ℝ ∞ (gaugeField P F n) (domain B.toData) :=
  contDiffOn_gaugeField hP

example (hP : ∀ t ∈ B.I, HasDerivAt P (B.a t ^ 2)⁻¹ t) (hPs : ContDiffOn ℝ ∞ P B.I)
    (hn : nsq n ≠ 0) (hz : z ∈ domain B.toData) :
    familyCoeffDeriv (pullbackFamily (metric B.toData) (gaugeField P F n)) z =
      metricPerturbation B (scalarMode n (fun t => -2 * F * nsq n * P t)
        (fun t => -2 * F * nsq n * P t + 6 * F * (deriv B.a t / B.a t))) z :=
  familyCoeffDeriv_pullback_gaugeField hP hPs hn hz

example {lam mu lam' mu' : ℝ → ℝ} (hl : lam (z 0) = lam' (z 0)) (hm : mu (z 0) = mu' (z 0)) :
    scalarMode n lam mu z = scalarMode n lam' mu' z :=
  scalarMode_congr hl hm

example {κ : ℝ} (hκ : κ ≠ 0) (hn : n ≠ 0) (F : ℝ) :
    (∀ z ∈ domain dustBackground.toData,
      familyCoeffDeriv (pullbackFamily (metric dustBackground.toData)
          (gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n)) z =
        metricPerturbation dustBackground (scalarMode n
          (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ))
          (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ) + 4 * F * t ^ (-1 : ℝ))) z ∧
      dustDensity κ (z 0) * (-2 * F * z 0 ^ (-1 : ℝ) * Real.cos (phase n z)) =
        fderiv ℝ (fun w => dustDensity κ (w 0)) z
          (gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n z) ∧
      fderiv ℝ (fun w => gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n w 0) z
          (Pi.single 0 1) = 0 ∧
      ∀ α : Fin 3, F * n α * Real.sin (phase n z) =
        -fderiv ℝ (fun w => gaugeField (fun t => -3 * t ^ (-1 / 3 : ℝ)) F n w 0) z
          (Pi.single α.succ 1)) ∧
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (scalarMode n (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ))
        (fun t => 6 * F * nsq n * t ^ (-1 / 3 : ℝ) + 4 * F * t ^ (-1 : ℝ)))
      (fun z => -2 * F * z 0 ^ (-1 : ℝ) * Real.cos (phase n z))
      fun z α => F * n α * Real.sin (phase n z) :=
  gaugeMode hκ hn F

example (c : ℝ) (n : Fin 3 → ℝ) (z : E) :
    E :=
  spatialGaugeField c n z

example (c : ℝ) (z v : E) :
    fderiv ℝ (fun w => spatialGaugeField c n w 0) z v = 0 :=
  fderiv_spatialGaugeField_zero c z v

example (c : ℝ) (γ : Fin 3) (z v : E) :
    fderiv ℝ (fun w => spatialGaugeField c n w γ.succ) z v =
      c / (2 * nsq n) * n γ * Real.cos (phase n z) * phaseCLM n v :=
  fderiv_spatialGaugeField_succ c γ z v

example (hn : nsq n ≠ 0) (hz : z ∈ domain B.toData) (c : ℝ) :
    coordinateLieMetric (spatialGaugeField c n) (metric B.toData) z =
      metricPerturbation B (scalarMode n (fun _ => c) fun _ => c) z :=
  coordinateLieMetric_spatialGaugeField hn hz c

example {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0))
    (hn : n ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust B κ ρ (scalarMode n (fun _ => c) fun _ => c) (fun _ => 0)
      (fun _ _ => 0) :=
  spatialGaugeMode hB hn c

end Gauge

section TensorVector

variable {κ : ℝ} {ρ : ℝ → ℝ} {n : Fin 3 → ℝ} {τ : ℝ → ℝ}

example (τ : ℝ → ℝ) (e : Fin 3 → Fin 3 → ℝ) (t : ℝ) (α β : Fin 3) :
    ℝ :=
  prodAmp τ e t α β

example (hτ : ContDiffOn ℝ ∞ τ B.I) {e : Fin 3 → Fin 3 → ℝ} (he : ∀ α β, e α β = e β α) :
    IsAmplitude B (prodAmp τ e) :=
  isAmplitude_prodAmp hτ he

example (hτ : ContDiffOn ℝ ∞ τ B.I) (e : Fin 3 → Fin 3 → ℝ) {t : ℝ} (ht : t ∈ B.I) (α β : Fin 3) :
    Fd (prodAmp τ e) t α β = deriv τ t * e α β :=
  Fd_prodAmp hτ e ht α β

example (hτ : ContDiffOn ℝ ∞ τ B.I) (e : Fin 3 → Fin 3 → ℝ) {t : ℝ} (ht : t ∈ B.I) (α β : Fin 3) :
    Fdd (prodAmp τ e) t α β = deriv (deriv τ) t * e α β :=
  Fdd_prodAmp hτ e ht α β

example {e : Fin 3 → Fin 3 → ℝ} (he : e ≠ 0) (X : ℝ) :
    (∀ α β, X * e α β = 0) ↔ X = 0 :=
  forall_mul_eq_zero_iff he X

example :
    Fin 3 → Fin 3 → ℝ :=
  plusPolarization

example :
    IsTensorPolarization ![0, 0, 1] plusPolarization :=
  isTensorPolarization_plus

example :
    plusPolarization ≠ 0 :=
  plusPolarization_ne_zero

example (n : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) (τ : ℝ → ℝ) :
    E → Fin 3 → Fin 3 → ℝ :=
  tensorMode n e τ

example (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0))
    (hn : n ≠ 0) {e : Fin 3 → Fin 3 → ℝ} (he : IsTensorPolarization n e) (he0 : e ≠ 0)
    (hτ : ContDiffOn ℝ ∞ τ B.I) :
    LinearizedEinsteinDust B κ ρ (tensorMode n e τ) (fun _ => 0) (fun _ _ => 0) ↔
      ∀ t ∈ B.I, deriv (deriv τ) t + 3 * (deriv B.a t / B.a t) * deriv τ t +
        nsq n / B.a t ^ 2 * τ t = 0 :=
  tensorMode_iff hB hn he he0 hτ

example (n e : Fin 3 → ℝ) (α β : Fin 3) :
    ℝ :=
  vectorAmp n e α β

example {e : Fin 3 → ℝ} (hn : nsq n ≠ 0) (he0 : e ≠ 0) (he : ∑ γ, n γ * e γ = 0) :
    vectorAmp n e ≠ 0 :=
  vectorAmp_ne_zero hn he0 he

example (n e : Fin 3 → ℝ) (σ : ℝ → ℝ) :
    E → Fin 3 → Fin 3 → ℝ :=
  vectorMode n e σ

example (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0))
    (hn : n ≠ 0) {e : Fin 3 → ℝ} (he : ∑ γ, n γ * e γ = 0) (he0 : e ≠ 0) {σ : ℝ → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ B.I) (w : ℝ → ℝ) :
    LinearizedEinsteinDust B κ ρ (vectorMode n e σ) (fun _ => 0)
        (fun z α => w (z 0) * e α * Real.cos (phase n z)) ↔
      ∀ t ∈ B.I, deriv (deriv σ) t + 3 * (deriv B.a t / B.a t) * deriv σ t = 0 ∧
        nsq n * deriv σ t = -(2 * κ * ρ t * w t) :=
  vectorMode_iff hB hn he he0 hσ w

example (hB : (metric B.toData).IsEinstein κ 0 (perfectFluidStress B.toData ρ fun _ => 0))
    (hI : IsPreconnected B.I) (hn : n ≠ 0) {e : Fin 3 → ℝ} (he : ∑ γ, n γ * e γ = 0) (he0 : e ≠ 0)
    {σ : ℝ → ℝ} (hσ : ContDiffOn ℝ ∞ σ B.I) (w : ℝ → ℝ)
    (hL : LinearizedEinsteinDust B κ ρ (vectorMode n e σ) (fun _ => 0)
      (fun z α => w (z 0) * e α * Real.cos (phase n z))) :
    ∃ C, ∀ t ∈ B.I, deriv σ t = C / B.a t ^ 3 ∧
      κ * ρ t * w t = -(nsq n * C) / (2 * B.a t ^ 3) :=
  vectorMode_decay hB hI hn he he0 hσ w hL

example (hκ : κ ≠ 0) (hn : n ≠ 0) {e : Fin 3 → ℝ} (he : ∑ γ, n γ * e γ = 0) (he0 : e ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust dustBackground κ (dustDensity κ)
      (vectorMode n e fun t => -c * t ^ (-1 : ℝ)) (fun _ => 0)
      (fun z α => -(3 * nsq n * c / 8) * e α * Real.cos (phase n z)) :=
  vectorMode_dust hκ hn he he0 c

example :
    (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 ∧ (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 ∧
      ∑ γ, (![0, 0, 1] : Fin 3 → ℝ) γ * (![1, 0, 0] : Fin 3 → ℝ) γ = 0 :=
  vectorMode_axis

end TensorVector

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation

end CosmologicalPerturbation

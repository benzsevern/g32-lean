module

public import HodgeLean.Foundations.Mathlib.FredholmAnalyticProofs

/-!
# Fredholm operators, analytic kernels and bounded holomorphic spaces (FROZEN SPEC)

Stage A of the relative-frame plan (`docs/specs/RelativeFrame.md`, §5), Mathlib only. It states:
Kato's implication from a finite-dimensional kernel and a range of finite algebraic codimension to
`IsFredholm`; local analytic Schur reduction at a Fredholm operator; local analytic kernel frames
for constant-dimension analytic Fredholm families and for constant-rank analytic matrix families;
the Banach space of bounded holomorphic functions on an open subset of `ℂ`, with its restriction,
composition and multiplication maps and their norm bounds; operator analyticity of multiplier
power series; the binomial multiplier on the annulus `A_n`; and joint analyticity of evaluation.
It claims nothing about Riemann surfaces, relative forms, the plumbing operator `δ_t` or its
Fredholm property, and nothing about the C8 reduction; those are later stages. HC no distance;
AV milestone no distance.
-/

@[expose] public noncomputable section

open Set Filter Topology Module
open scoped BoundedContinuousFunction

namespace HodgeLean.Foundations

/-- A bounded operator between complex Banach spaces whose kernel is finite-dimensional and whose
range has finite algebraic codimension is Fredholm: no closed-range hypothesis is assumed.
Source: Kato, *Perturbation Theory for Linear Operators*, 2nd ed. (1976), Ch. IV, §5.1;
Gohberg–Goldberg–Kaashoek, *Classes of Linear Operators I* (1990), Ch. XI. -/
theorem b63r_isFredholm_of_finite {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hker : FiniteDimensional ℂ T.ker)
    (hcoker : T.range.CoFG) :
    T.IsFredholm :=
  b63r_isFredholm_of_finite_aux T hker hcoker

example {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hker : FiniteDimensional ℂ T.ker)
    (hcoker : T.range.CoFG) :
    T.IsFredholm :=
  b63r_isFredholm_of_finite T hker hcoker

/-- Local Schur reduction at a Fredholm operator `T₀`: on an open neighbourhood of `T₀` there are
analytic maps `M(S)` from `ker T₀` to the cokernel of `T₀` (both in coordinates) and `L(S)` from
`ker T₀` to `E`, with `M(T₀) = 0`, each `L(S)` injective and `L(S)(ker M(S)) = ker S`.
Source: Gohberg–Goldberg–Kaashoek, *Classes of Linear Operators I* (1990), Ch. XI;
Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Ch. IV, §5. -/
theorem b63r_fredholm_schur {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm) :
    ∃ 𝒰 : Set (E →L[ℂ] F), IsOpen 𝒰 ∧ T₀ ∈ 𝒰 ∧
      ∃ (M : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ]
          (Fin (finrank ℂ (F ⧸ T₀.range)) → ℂ))
        (L : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ] E),
        AnalyticOnNhd ℂ M 𝒰 ∧ AnalyticOnNhd ℂ L 𝒰 ∧ M T₀ = 0 ∧
        ∀ S ∈ 𝒰, Function.Injective (L S) ∧
          (M S).ker.map (L S).toLinearMap = S.ker :=
  b63r_fredholm_schur_aux T₀ hT₀

example {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm) :
    ∃ 𝒰 : Set (E →L[ℂ] F), IsOpen 𝒰 ∧ T₀ ∈ 𝒰 ∧
      ∃ (M : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ]
          (Fin (finrank ℂ (F ⧸ T₀.range)) → ℂ))
        (L : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ] E),
        AnalyticOnNhd ℂ M 𝒰 ∧ AnalyticOnNhd ℂ L 𝒰 ∧ M T₀ = 0 ∧
        ∀ S ∈ 𝒰, Function.Injective (L S) ∧
          (M S).ker.map (L S).toLinearMap = S.ker :=
  b63r_fredholm_schur T₀ hT₀

/-- An operator-norm analytic family on an open `W ⊆ ℂᵏ`, Fredholm at `t₀ ∈ W`, whose kernels all
have dimension `d` on `W`, has `d` analytic kernel vectors near `t₀`, independent and spanning
each kernel.
Source: Gohberg–Goldberg–Kaashoek, *Classes of Linear Operators I* (1990), Ch. XI;
Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Ch. VII, §1. -/
theorem b63r_analytic_kernel_frame {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {k d : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W) (T : (Fin k → ℂ) → E →L[ℂ] F)
    (hT : AnalyticOnNhd ℂ T W) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) (hF : (T t₀).IsFredholm)
    (hd : ∀ t ∈ W, finrank ℂ ((T t).ker) = d) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ e : Fin d → (Fin k → ℂ) → E, (∀ i, AnalyticOnNhd ℂ (e i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ e i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ e i t) = (T t).ker :=
  b63r_analytic_kernel_frame_aux W hW T hT t₀ ht₀ hF hd

example {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {k d : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W) (T : (Fin k → ℂ) → E →L[ℂ] F)
    (hT : AnalyticOnNhd ℂ T W) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) (hF : (T t₀).IsFredholm)
    (hd : ∀ t ∈ W, finrank ℂ ((T t).ker) = d) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ e : Fin d → (Fin k → ℂ) → E, (∀ i, AnalyticOnNhd ℂ (e i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ e i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ e i t) = (T t).ker :=
  b63r_analytic_kernel_frame W hW T hT t₀ ht₀ hF hd

/-- A constant-rank analytic family of `p × q` complex matrices on an open `W ⊆ ℂᵏ` has, near each
`t₀ ∈ W`, `q − ρ` analytic kernel vectors, independent and spanning each kernel.
Source: Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Ch. II, §4. -/
theorem b63r_matrix_kernel_frame {k p q ρ : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin p) (Fin q) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun t ↦ M t i j) W)
    (hρ : ∀ t ∈ W, (M t).rank = ρ) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ v : Fin (q - ρ) → (Fin k → ℂ) → (Fin q → ℂ), (∀ i, AnalyticOnNhd ℂ (v i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ v i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ v i t) = LinearMap.ker (M t).mulVecLin :=
  b63r_matrix_kernel_frame_aux W hW M hM hρ t₀ ht₀

example {k p q ρ : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin p) (Fin q) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun t ↦ M t i j) W)
    (hρ : ∀ t ∈ W, (M t).rank = ρ) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ v : Fin (q - ρ) → (Fin k → ℂ) → (Fin q → ℂ), (∀ i, AnalyticOnNhd ℂ (v i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ v i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ v i t) = LinearMap.ker (M t).mulVecLin :=
  b63r_matrix_kernel_frame W hW M hM hρ t₀ ht₀

open Classical in
/-- On an open `U`, a bounded continuous function lies in `b63r_bddHol U` exactly when its extension
by zero is holomorphic on `U`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 10 and Ch. 17. -/
theorem b63r_mem_bddHol_iff {U : Set ℂ} (hU : IsOpen U) (f : U →ᵇ ℂ) :
    f ∈ b63r_bddHol U ↔
      DifferentiableOn ℂ (fun z ↦ if h : z ∈ U then f ⟨z, h⟩ else 0) U :=
  b63r_mem_bddHol_iff_aux hU f

open Classical in
example {U : Set ℂ} (hU : IsOpen U) (f : U →ᵇ ℂ) :
    f ∈ b63r_bddHol U ↔
      DifferentiableOn ℂ (fun z ↦ if h : z ∈ U then f ⟨z, h⟩ else 0) U :=
  b63r_mem_bddHol_iff hU f

/-- On an open `U`, a uniform limit of bounded holomorphic functions is bounded holomorphic.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.28 (Weierstrass). -/
theorem b63r_bddHol_limit {U : Set ℂ} (hU : IsOpen U) (F : ℕ → U →ᵇ ℂ)
    (hF : ∀ n, F n ∈ b63r_bddHol U) (f : U →ᵇ ℂ) (hlim : Tendsto F atTop (𝓝 f)) :
    f ∈ b63r_bddHol U :=
  b63r_bddHol_limit_aux hU F hF f hlim

example {U : Set ℂ} (hU : IsOpen U) (F : ℕ → U →ᵇ ℂ)
    (hF : ∀ n, F n ∈ b63r_bddHol U) (f : U →ᵇ ℂ) (hlim : Tendsto F atTop (𝓝 f)) :
    f ∈ b63r_bddHol U :=
  b63r_bddHol_limit hU F hF f hlim

/-- On an open `U`, the bounded holomorphic functions with the sup norm form a Banach space.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.28 and Ch. 17;
Rudin, *Functional Analysis*, 2nd ed., Ch. 1 (closed subspaces of Banach spaces). -/
theorem b63r_bddHol_completeSpace {U : Set ℂ} (hU : IsOpen U) :
    CompleteSpace (b63r_bddHol U) :=
  b63r_bddHol_completeSpace_aux hU

example {U : Set ℂ} (hU : IsOpen U) :
    CompleteSpace (b63r_bddHol U) :=
  b63r_bddHol_completeSpace hU

/-- Restriction from `U` to `U' ⊆ U` is evaluation at the included point and has norm at most one.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 17 (sup over a subset). -/
theorem b63r_bddHol_restrict_spec {U U' : Set ℂ} (h : U' ⊆ U) :
    ‖b63r_bddHol_restrict h‖ ≤ 1 ∧
      ∀ (f : b63r_bddHol U) (z : U'),
        ((b63r_bddHol_restrict h f : b63r_bddHol U') : U' →ᵇ ℂ) z =
          (f : U →ᵇ ℂ) (inclusion h z) :=
  b63r_bddHol_restrict_spec_aux h

example {U U' : Set ℂ} (h : U' ⊆ U) :
    ‖b63r_bddHol_restrict h‖ ≤ 1 ∧
      ∀ (f : b63r_bddHol U) (z : U'),
        ((b63r_bddHol_restrict h f : b63r_bddHol U') : U' →ᵇ ℂ) z =
          (f : U →ᵇ ℂ) (inclusion h z) :=
  b63r_bddHol_restrict_spec h

/-- Composition with a holomorphic `ψ` mapping `U'` into `U` is evaluation at `ψ z` and has norm at
most one.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 10 and Ch. 17. -/
theorem b63r_bddHol_comp_spec {U U' : Set ℂ} (ψ : ℂ → ℂ) (hψ : DifferentiableOn ℂ ψ U')
    (hmaps : MapsTo ψ U' U) :
    ‖b63r_bddHol_comp ψ hψ hmaps‖ ≤ 1 ∧
      ∀ (f : b63r_bddHol U) (z : U'),
        ((b63r_bddHol_comp ψ hψ hmaps f : b63r_bddHol U') : U' →ᵇ ℂ) z =
          (f : U →ᵇ ℂ) ⟨ψ z, hmaps z.2⟩ :=
  b63r_bddHol_comp_spec_aux ψ hψ hmaps

example {U U' : Set ℂ} (ψ : ℂ → ℂ) (hψ : DifferentiableOn ℂ ψ U')
    (hmaps : MapsTo ψ U' U) :
    ‖b63r_bddHol_comp ψ hψ hmaps‖ ≤ 1 ∧
      ∀ (f : b63r_bddHol U) (z : U'),
        ((b63r_bddHol_comp ψ hψ hmaps f : b63r_bddHol U') : U' →ᵇ ℂ) z =
          (f : U →ᵇ ℂ) ⟨ψ z, hmaps z.2⟩ :=
  b63r_bddHol_comp_spec ψ hψ hmaps

/-- Multiplication by a bounded holomorphic `m` is pointwise and has norm at most `‖m‖`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 17; Rudin, *Functional Analysis*,
2nd ed., §10.1 (Banach algebras). -/
theorem b63r_bddHol_mul_spec {U : Set ℂ} (m : b63r_bddHol U) :
    ‖b63r_bddHol_mul m‖ ≤ ‖m‖ ∧
      ∀ (f : b63r_bddHol U) (z : U),
        ((b63r_bddHol_mul m f : b63r_bddHol U) : U →ᵇ ℂ) z =
          (m : U →ᵇ ℂ) z * (f : U →ᵇ ℂ) z :=
  b63r_bddHol_mul_spec_aux m

example {U : Set ℂ} (m : b63r_bddHol U) :
    ‖b63r_bddHol_mul m‖ ≤ ‖m‖ ∧
      ∀ (f : b63r_bddHol U) (z : U),
        ((b63r_bddHol_mul m f : b63r_bddHol U) : U →ᵇ ℂ) z =
          (m : U →ᵇ ℂ) z * (f : U →ᵇ ℂ) z :=
  b63r_bddHol_mul_spec m

/-- On an open `U`, if `Σ ρᵏ ‖c_k‖ < ∞` with `ρ > 0`, then `Σ εᵏ · mul(c_k)` converges in operator
norm for `‖ε‖ < ρ` and is analytic there.
Source: Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Ch. III, §3.1
(vector-valued power series). -/
theorem b63r_mulSeries_analytic {U : Set ℂ} (hU : IsOpen U) (c : ℕ → b63r_bddHol U)
    (ρ : ℝ) (hρ : 0 < ρ) (hc : Summable fun k ↦ ρ ^ k * ‖c k‖) :
    (∀ ε ∈ Metric.ball (0 : ℂ) ρ, Summable fun k ↦ ε ^ k • b63r_bddHol_mul (c k)) ∧
      AnalyticOnNhd ℂ (fun ε : ℂ ↦ ∑' k, ε ^ k • b63r_bddHol_mul (c k))
        (Metric.ball (0 : ℂ) ρ) :=
  b63r_mulSeries_analytic_aux hU c ρ hρ hc

example {U : Set ℂ} (hU : IsOpen U) (c : ℕ → b63r_bddHol U)
    (ρ : ℝ) (hρ : 0 < ρ) (hc : Summable fun k ↦ ρ ^ k * ‖c k‖) :
    (∀ ε ∈ Metric.ball (0 : ℂ) ρ, Summable fun k ↦ ε ^ k • b63r_bddHol_mul (c k)) ∧
      AnalyticOnNhd ℂ (fun ε : ℂ ↦ ∑' k, ε ^ k • b63r_bddHol_mul (c k))
        (Metric.ball (0 : ℂ) ρ) :=
  b63r_mulSeries_analytic hU c ρ hρ hc

/-- For `n ≥ 1`, `r > 0` and `‖ε‖ < r`, on the annulus `A_n = {r < |u|ⁿ < 2r}` the principal branch
of `(1 − εu⁻ⁿ)^s` is the binomial series `Σ binom(s, k) (−ε)ᵏ u^(−nk)`, and the supremum of
`|u^(−nk)|` over `A_n` is `r^(−k)`.
Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 5, §2 (power series of the
principal branch); Mathlib `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`. -/
theorem b63r_binomial_multiplier (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    (∀ (s ε : ℂ), ‖ε‖ < r → ∀ u ∈ b63r_annulus n r,
      HasSum (fun k : ℕ ↦ Ring.choose s k * (-ε) ^ k * u ^ (-((n * k : ℕ) : ℤ)))
        ((1 - ε * u ^ (-(n : ℤ))) ^ s)) ∧
      ∀ k : ℕ, IsLUB ((fun u : ℂ ↦ ‖u ^ (-((n * k : ℕ) : ℤ))‖) '' b63r_annulus n r)
        (r ^ (-(k : ℤ))) :=
  b63r_binomial_multiplier_aux n hn r hr

example (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    (∀ (s ε : ℂ), ‖ε‖ < r → ∀ u ∈ b63r_annulus n r,
      HasSum (fun k : ℕ ↦ Ring.choose s k * (-ε) ^ k * u ^ (-((n * k : ℕ) : ℤ)))
        ((1 - ε * u ^ (-(n : ℤ))) ^ s)) ∧
      ∀ k : ℕ, IsLUB ((fun u : ℂ ↦ ‖u ^ (-((n * k : ℕ) : ℤ))‖) '' b63r_annulus n r)
        (r ^ (-(k : ℤ))) :=
  b63r_binomial_multiplier n hn r hr

open Classical in
/-- An analytic map from an open `W ⊆ ℂᵏ` into the bounded holomorphic functions on an open `U`
has jointly analytic evaluation on `W × U`.
Source: Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Ch. III, §3.1;
Gunning–Rossi, *Analytic Functions of Several Complex Variables* (1965), Ch. I, §A (Osgood). -/
theorem b63r_eval_analytic {k : ℕ} {U : Set ℂ} (hU : IsOpen U) (W : Set (Fin k → ℂ))
    (hW : IsOpen W) (e : (Fin k → ℂ) → b63r_bddHol U) (he : AnalyticOnNhd ℂ e W) :
    AnalyticOnNhd ℂ
      (fun p : (Fin k → ℂ) × ℂ ↦ if h : p.2 ∈ U then ((e p.1 : b63r_bddHol U) : U →ᵇ ℂ) ⟨p.2, h⟩
        else 0) (W ×ˢ U) :=
  b63r_eval_analytic_aux hU W hW e he

open Classical in
example {k : ℕ} {U : Set ℂ} (hU : IsOpen U) (W : Set (Fin k → ℂ))
    (hW : IsOpen W) (e : (Fin k → ℂ) → b63r_bddHol U) (he : AnalyticOnNhd ℂ e W) :
    AnalyticOnNhd ℂ
      (fun p : (Fin k → ℂ) × ℂ ↦ if h : p.2 ∈ U then ((e p.1 : b63r_bddHol U) : U →ᵇ ℂ) ⟨p.2, h⟩
        else 0) (W ×ˢ U) :=
  b63r_eval_analytic hU W hW e he

end HodgeLean.Foundations

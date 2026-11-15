import HodgeLean.Foundations.Program.SchlesingerPathProofs
import HodgeLean.Foundations.Program.BraidCertificate
import HodgeLean.Papers.G32DominanceDefs

/-! # B6-5 stage 5c: the Schlesinger deformation and the path in the chart

Implication from holomorphic pole paths and initial residues to a holomorphic isomonodromic
Schlesinger deformation with persistent fixed-pole normal forms (three general statements);
and, for the twelve labelled reflection poles in the certified boxes, the identification of the
base system with the printed pullback, its fixed-pole normal forms, constancy of the certified
marked monodromy along the deformation in the direction `(V₅, V₋₇)` of G32 Proposition 5.9, the
normalization of three branch points to `0, 1, ∞`, the resulting path in `b6_chart` with the
field types of `g32r_PeriodMap.curve_cont` and `.curve_zero`, and the record `b65p_Outputs` of
the outputs that stage 5d consumes.

Not claimed: the differential dictionary, the kernel frames or numerators along the path (5d),
the certified jet (5e), the codifferential (B6-6), any field of `g32r_PeriodMap` other than
`curve`, `curve_cont` and `curve_zero`, or that the covers along the path are fibres of any
particular family. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- **Schlesinger deformations are isomonodromic** (the plan's `b65_schlesinger_isomonodromic`).
For holomorphic distinct poles and residues solving the Schlesinger equations on a disc, the
residue sum is constant, each residue stays conjugate to its initial value, and for every base
point there is one operator conjugating the transport at `θ` to the transport at `0` along every
loop that avoids the poles over the whole disc. Mathlib-only.
Source: Schlesinger, J. reine angew. Math. 141 (1912); Jimbo–Miwa–Ueno, Physica D 2 (1981), §2;
G32 v0.16, Lemma 5.6 (1)–(2). -/
theorem b65p_schlesinger_isomonodromic (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) :
    (∀ θ ∈ ball (0 : ℂ) r, ∑ q, A θ q = ∑ q, A 0 q) ∧
    (∀ θ ∈ ball (0 : ℂ) r, ∀ q, ∃ G : (E →L[ℂ] E)ˣ, A θ q = G.val * A 0 q * (G⁻¹).val) ∧
    ∀ x : ℂ, ∀ θ ∈ ball (0 : ℂ) r, ∃ G : (E →L[ℂ] E)ˣ, ∀ γ : Path x x,
      (∀ θ' ∈ ball (0 : ℂ) r, ∀ s q, γ s ≠ t θ' q) →
      b65f_transport E (b65p_coefficient E (t θ) (A θ)) (fun u ↦ γ.extend u) =
        G.val * b65f_transport E (b65p_coefficient E (t 0) (A 0)) (fun u ↦ γ.extend u) *
          (G⁻¹).val :=
  b65p_schlesinger_isomonodromic_aux E r t A ht hinj hA

example (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) :
    (∀ θ ∈ ball (0 : ℂ) r, ∑ q, A θ q = ∑ q, A 0 q) ∧
    (∀ θ ∈ ball (0 : ℂ) r, ∀ q, ∃ G : (E →L[ℂ] E)ˣ, A θ q = G.val * A 0 q * (G⁻¹).val) ∧
    ∀ x : ℂ, ∀ θ ∈ ball (0 : ℂ) r, ∃ G : (E →L[ℂ] E)ˣ, ∀ γ : Path x x,
      (∀ θ' ∈ ball (0 : ℂ) r, ∀ s q, γ s ≠ t θ' q) →
      b65f_transport E (b65p_coefficient E (t θ) (A θ)) (fun u ↦ γ.extend u) =
        G.val * b65f_transport E (b65p_coefficient E (t 0) (A 0)) (fun u ↦ γ.extend u) *
          (G⁻¹).val :=
  b65p_schlesinger_isomonodromic E r t A ht hinj hA

/-- **Existence and uniqueness of the Schlesinger deformation.** For holomorphic pole paths,
distinct at `θ = 0`, and arbitrary initial residues, the Schlesinger equations have a holomorphic
solution on a disc on which the poles stay distinct, and it is the only solution with those
initial residues on every smaller disc. Mathlib-only.
Source: G32 v0.16, Lemma 5.6, first sentence and proof; Hille, Ordinary Differential Equations in
the Complex Domain, §2.3 (holomorphic Cauchy problem); `b65_holomorphic_ode`. -/
theorem b65p_schlesinger_solution (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : Function.Injective (t 0)) (A₀ : ι → E →L[ℂ] E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ A : ℂ → ι → E →L[ℂ] E,
      A 0 = A₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ρ, Function.Injective (t θ)) ∧
      (∀ q, AnalyticOnNhd ℂ (fun θ ↦ A θ q) (ball 0 ρ)) ∧
      (∀ θ ∈ ball (0 : ℂ) ρ, ∀ p, HasDerivAt (fun θ ↦ A θ p)
        (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) ∧
      ∀ ρ' : ℝ, ρ' ≤ ρ → ∀ B : ℂ → ι → E →L[ℂ] E, B 0 = A₀ →
        (∀ θ ∈ ball (0 : ℂ) ρ', ∀ p, HasDerivAt (fun θ ↦ B θ p)
          (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (B θ) p) θ) →
        ∀ θ ∈ ball (0 : ℂ) ρ', B θ = A θ :=
  b65p_schlesinger_solution_aux E r hr t ht hinj A₀

example (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : Function.Injective (t 0)) (A₀ : ι → E →L[ℂ] E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ A : ℂ → ι → E →L[ℂ] E,
      A 0 = A₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ρ, Function.Injective (t θ)) ∧
      (∀ q, AnalyticOnNhd ℂ (fun θ ↦ A θ q) (ball 0 ρ)) ∧
      (∀ θ ∈ ball (0 : ℂ) ρ, ∀ p, HasDerivAt (fun θ ↦ A θ p)
        (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) ∧
      ∀ ρ' : ℝ, ρ' ≤ ρ → ∀ B : ℂ → ι → E →L[ℂ] E, B 0 = A₀ →
        (∀ θ ∈ ball (0 : ℂ) ρ', ∀ p, HasDerivAt (fun θ ↦ B θ p)
          (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (B θ) p) θ) →
        ∀ θ ∈ ball (0 : ℂ) ρ', B θ = A θ :=
  b65p_schlesinger_solution E r hr t ht hinj A₀

/-- **Normal forms at a fixed pole persist.** If a pole does not move and the system at `θ = 0`
has the normal form `P₀ H₀(s) (s − t_p)^Λ` there, then on a smaller bidisc the system at `θ` has
a normal form `P(θ) H(s, θ) (s − t_p)^Λ` with `P` and `H` holomorphic, `P(0) = P₀`,
`H(s, 0) = H₀(s)` and `H(t_p, θ) = 1`; `P(θ)` is an eigenbasis of the residue with the same `Λ`.
Mathlib-only.
Source: G32 v0.16, Lemma 5.6 (3) and its proof; Jimbo–Miwa–Ueno, Physica D 2 (1981), §2. -/
theorem b65p_schlesinger_fixed_pole (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ)
    (p : ι) (hp : ∀ θ ∈ ball (0 : ℂ) r, t θ p = t 0 p)
    (Λ P₀ : E →L[ℂ] E) (hP₀ : IsUnit P₀) (hΛ : A 0 p * P₀ = P₀ * Λ)
    (d : ℝ) (hd : 0 < d) (H₀ : ℂ → E →L[ℂ] E)
    (hH₀ : AnalyticOnNhd ℂ H₀ (ball (t 0 p) d)) (hH₀p : H₀ (t 0 p) = 1)
    (hH₀eq : ∀ s ∈ ball (t 0 p) d,
      (s - t 0 p) • deriv H₀ s = Λ * H₀ s - H₀ s * Λ +
        (s - t 0 p) • ((Ring.inverse P₀ * b65p_regularPart E (t 0) (A 0) p s * P₀) * H₀ s)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ε ≤ d ∧
    ∃ P : ℂ → E →L[ℂ] E, ∃ H : ℂ → ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ P (ball 0 ε) ∧ P 0 = P₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ε, IsUnit (P θ) ∧ A θ p * P θ = P θ * Λ) ∧
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ ↦ H w.1 w.2) (ball (t 0 p) ε ×ˢ ball 0 ε) ∧
      (∀ s ∈ ball (t 0 p) ε, H s 0 = H₀ s) ∧
      (∀ θ ∈ ball (0 : ℂ) ε, H (t 0 p) θ = 1) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, ∀ s ∈ ball (t 0 p) ε,
        (s - t 0 p) • deriv (fun s ↦ H s θ) s = Λ * H s θ - H s θ * Λ +
          (s - t 0 p) • ((Ring.inverse (P θ) * b65p_regularPart E (t θ) (A θ) p s * P θ) *
            H s θ) :=
  b65p_schlesinger_fixed_pole_aux E r hr t A ht hinj hA p hp Λ P₀ hP₀ hΛ d hd H₀ hH₀ hH₀p hH₀eq

example (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ)
    (p : ι) (hp : ∀ θ ∈ ball (0 : ℂ) r, t θ p = t 0 p)
    (Λ P₀ : E →L[ℂ] E) (hP₀ : IsUnit P₀) (hΛ : A 0 p * P₀ = P₀ * Λ)
    (d : ℝ) (hd : 0 < d) (H₀ : ℂ → E →L[ℂ] E)
    (hH₀ : AnalyticOnNhd ℂ H₀ (ball (t 0 p) d)) (hH₀p : H₀ (t 0 p) = 1)
    (hH₀eq : ∀ s ∈ ball (t 0 p) d,
      (s - t 0 p) • deriv H₀ s = Λ * H₀ s - H₀ s * Λ +
        (s - t 0 p) • ((Ring.inverse P₀ * b65p_regularPart E (t 0) (A 0) p s * P₀) * H₀ s)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ε ≤ d ∧
    ∃ P : ℂ → E →L[ℂ] E, ∃ H : ℂ → ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ P (ball 0 ε) ∧ P 0 = P₀ ∧
      (∀ θ ∈ ball (0 : ℂ) ε, IsUnit (P θ) ∧ A θ p * P θ = P θ * Λ) ∧
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ ↦ H w.1 w.2) (ball (t 0 p) ε ×ˢ ball 0 ε) ∧
      (∀ s ∈ ball (t 0 p) ε, H s 0 = H₀ s) ∧
      (∀ θ ∈ ball (0 : ℂ) ε, H (t 0 p) θ = 1) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, ∀ s ∈ ball (t 0 p) ε,
        (s - t 0 p) • deriv (fun s ↦ H s θ) s = Λ * H s θ - H s θ * Λ +
          (s - t 0 p) • ((Ring.inverse (P θ) * b65p_regularPart E (t θ) (A θ) p s * P θ) *
            H s θ) :=
  b65p_schlesinger_fixed_pole E r hr t A ht hinj hA p hp Λ P₀ hP₀ hΛ d hd H₀ hH₀ hH₀p hH₀eq

/-- **The base system.** For the twelve labelled roots in the certified boxes, the sixteen poles
are distinct, they are exactly the complement of `b65s_regular`, and the indexed coefficient with
the base residues is the printed pullback coefficient on `b65s_regular`.
Source: G32 v0.16, §5.2 (P₅, P₋₇) and §5.5, first paragraph; `b65r_pullback`;
B65-BRAIDCERT checker A (boxes). -/
theorem b65p_base_system (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    Function.Injective (b65p_poles p 0) ∧
    (∀ s : ℂ, s ∈ b65s_regular ↔ ∀ q, s ≠ b65p_poles p 0 q) ∧
    ∀ s ∈ b65s_regular,
      b65p_coefficient (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue s = b65r_pullback s :=
  b65p_base_system_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    Function.Injective (b65p_poles p 0) ∧
    (∀ s : ℂ, s ∈ b65s_regular ↔ ∀ q, s ≠ b65p_poles p 0 q) ∧
    ∀ s ∈ b65s_regular,
      b65p_coefficient (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue s = b65r_pullback s :=
  b65p_base_system p hp

/-- **Normal forms of the base system at the fixed poles.** At `0, 3, 1, −2`, for every eigenbasis
`P₀` of the base residue in the increasing exponent order, the base system has a normal form
`P₀ H₀(s) (s − p)^Λ` with `H₀` holomorphic and `H₀(p) = 1`.
Source: G32 v0.16, Lemma 5.7 (lem:normalform) and its proof by pulling back the nonresonant
four-point system; §5.3, the local form. -/
theorem b65p_base_normal_form (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (k : Fin 4) (P₀ : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (hP₀ : IsUnit P₀)
    (hΛ : b65p_initialResidue (Sum.inl k) * P₀ = P₀ * b65p_exponent k) :
    ∃ d : ℝ, 0 < d ∧ ∃ H₀ : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      AnalyticOnNhd ℂ H₀ (ball (b65p_fixedPole k) d) ∧ H₀ (b65p_fixedPole k) = 1 ∧
      ∀ s ∈ ball (b65p_fixedPole k) d,
        (s - b65p_fixedPole k) • deriv H₀ s =
          b65p_exponent k * H₀ s - H₀ s * b65p_exponent k +
            (s - b65p_fixedPole k) • ((Ring.inverse P₀ *
              b65p_regularPart (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue (Sum.inl k) s *
                P₀) * H₀ s) :=
  b65p_base_normal_form_aux p hp k P₀ hP₀ hΛ

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (k : Fin 4) (P₀ : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (hP₀ : IsUnit P₀)
    (hΛ : b65p_initialResidue (Sum.inl k) * P₀ = P₀ * b65p_exponent k) :
    ∃ d : ℝ, 0 < d ∧ ∃ H₀ : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ),
      AnalyticOnNhd ℂ H₀ (ball (b65p_fixedPole k) d) ∧ H₀ (b65p_fixedPole k) = 1 ∧
      ∀ s ∈ ball (b65p_fixedPole k) d,
        (s - b65p_fixedPole k) • deriv H₀ s =
          b65p_exponent k * H₀ s - H₀ s * b65p_exponent k +
            (s - b65p_fixedPole k) • ((Ring.inverse P₀ *
              b65p_regularPart (Fin 4 → ℂ) (b65p_poles p 0) b65p_initialResidue (Sum.inl k) s *
                P₀) * H₀ s) :=
  b65p_base_normal_form p hp k P₀ hP₀ hΛ

/-- **The certified marked monodromy is constant along the deformation.** For every Schlesinger
solution with the base residues and every certified marking `(x, γ, C)` of the base system (the
shape of `b65b_transported_identification`), for small `θ` the loops avoid the moving poles and
one operator `C_θ` conjugates the decoded final certificate tuple to the transport at `θ` in every
slot.
Source: G32 v0.16, Lemma 5.6 (2) and §5.5 ("C_θ lies on the component Hur° of C₀");
`docs/specs/BraidCertificate.md`, statement 8. -/
theorem b65p_marked_monodromy (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (r : ℝ) (hr : 0 < r) (A : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (hA0 : A 0 = b65p_initialResidue)
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ q, HasDerivAt (fun θ ↦ A θ q)
      (b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ) (A θ) q) θ)
    (x : b65s_regular) (γ : Fin 13 → Path x x) (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ i, b65p_certifiedTransport x γ i =
      C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∀ θ ∈ ball (0 : ℂ) r',
      (∀ i s q, ((γ i s : b65s_regular) : ℂ) ≠ b65p_poles p θ q) ∧
      ∃ Cθ : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ i,
        b65f_transport (Fin 4 → ℂ) (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (A θ))
            (fun u ↦ ((γ i.rev).extend u).val) =
          Cθ.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (Cθ⁻¹).val :=
  b65p_marked_monodromy_aux p hp r hr A hA0 hA x γ C hT

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (r : ℝ) (hr : 0 < r) (A : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    (hA0 : A 0 = b65p_initialResidue)
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ q, HasDerivAt (fun θ ↦ A θ q)
      (b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ) (A θ) q) θ)
    (x : b65s_regular) (γ : Fin 13 → Path x x) (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ i, b65p_certifiedTransport x γ i =
      C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∀ θ ∈ ball (0 : ℂ) r',
      (∀ i s q, ((γ i s : b65s_regular) : ℂ) ≠ b65p_poles p θ q) ∧
      ∃ Cθ : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ i,
        b65f_transport (Fin 4 → ℂ) (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (A θ))
            (fun u ↦ ((γ i.rev).extend u).val) =
          Cθ.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (Cθ⁻¹).val :=
  b65p_marked_monodromy p hp r hr A hA0 hA x γ C hT

/-- **Normalization and the path in the chart.** For small `θ`, the Möbius map sending the
branch points labelled 10 and 11 to `0` and `1` and the branch point `0` to `∞` is a homeomorphism
of the sphere carrying the thirteen branch points at `θ` to `b6_branch (b65p_curve p θ)`, which is
in `b6_chart`. The path is holomorphic at `0` with nonzero derivative, continuous at `0`, its base
point lies in the polydisc `b6t_polydisc (b65p_curve p 0)`, and it stays there for small `θ`.
Source: G32 v0.16, §3.1 (normalization modulo PGL₂) and §5.5 (The direction); Proposition 5.9
(V₅, V₋₇); `g32r_PeriodMap.curve_cont`, `.curve_zero`; `b6t_polydisc_neighbourhood`. -/
theorem b65p_normalized_path (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    (∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6_chart ∧
      ∃ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
        ⇑M = b65p_mobius (b65p_moving p θ 10) (b65p_moving p θ 11) ∧
          ∀ k, M (b65p_source p θ k) = b6_branch (b65p_curve p θ) k) ∧
    AnalyticAt ℂ (b65p_curve p) 0 ∧ deriv (b65p_curve p) 0 ≠ 0 ∧
    ContinuousAt (b65p_curve p) 0 ∧
    b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0) ∧
    ∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6t_polydisc (b65p_curve p 0) :=
  b65p_normalized_path_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    (∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6_chart ∧
      ∃ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
        ⇑M = b65p_mobius (b65p_moving p θ 10) (b65p_moving p θ 11) ∧
          ∀ k, M (b65p_source p θ k) = b6_branch (b65p_curve p θ) k) ∧
    AnalyticAt ℂ (b65p_curve p) 0 ∧ deriv (b65p_curve p) 0 ≠ 0 ∧
    ContinuousAt (b65p_curve p) 0 ∧
    b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0) ∧
    ∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6t_polydisc (b65p_curve p 0) :=
  b65p_normalized_path p hp

/-- **The stage 5c outputs.** For the twelve labelled roots in the certified boxes, the record
`b65p_Outputs p` consumed by stage 5d is inhabited.
Source: G32 v0.16, Lemmas 5.6 and 5.7 and §5.5 (The direction); assembly of the six preceding
statements of this file with `b65p_schlesinger_fixed_pole`. -/
theorem b65p_outputs (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    Nonempty (b65p_Outputs p) :=
  b65p_outputs_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    Nonempty (b65p_Outputs p) :=
  b65p_outputs p hp

/-- **Hypothesis check for the general statements, rank four and moving poles.** Constant scalar
residues `c_q • 1` with `c = (1, 2)` solve the Schlesinger equations along the moving poles
`(0, 1 + θ)`, which stay distinct on the disc of radius one. -/
example : ∀ θ ∈ ball (0 : ℂ) 1, ∀ q : Fin 2,
    HasDerivAt (fun _ : ℂ ↦ (fun q : Fin 2 ↦ (![1, 2] q : ℂ) •
        (1 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))) q)
      (b65p_schlesingerField (Fin 4 → ℂ)
        (fun q ↦ deriv (fun θ : ℂ ↦ (![0, 1 + θ] : Fin 2 → ℂ) q) θ) ![0, 1 + θ]
        (fun q : Fin 2 ↦ (![1, 2] q : ℂ) • (1 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))) q) θ := by
  intro θ _ q
  have h0 : b65p_schlesingerField (Fin 4 → ℂ)
      (fun q ↦ deriv (fun θ : ℂ ↦ (![0, 1 + θ] : Fin 2 → ℂ) q) θ) ![0, 1 + θ]
      (fun q : Fin 2 ↦ (![1, 2] q : ℂ) • (1 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))) q = 0 := by
    simp [b65p_schlesingerField, smul_smul, mul_comm]
  rw [h0]
  exact hasDerivAt_const θ _

example : ∀ θ ∈ ball (0 : ℂ) 1, Function.Injective (![0, 1 + θ] : Fin 2 → ℂ) := by
  intro θ hθ i j hij
  have hθ' : ‖θ‖ < 1 := by simpa using hθ
  have hne : (1 + θ : ℂ) ≠ 0 := by
    intro h
    have : θ = -1 := by linear_combination h
    rw [this] at hθ'
    norm_num at hθ'
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- **Hypothesis check for `b65p_schlesinger_fixed_pole`, rank four.** One fixed pole at `0` with
the nonzero diagonal residue `Λ = b65p_exponent 0`, the eigenbasis `1` and `H₀ = 1` satisfy the
normal-form hypotheses: the regular part vanishes. -/
example : ∀ s ∈ ball (0 : ℂ) 1,
    (s - 0) • deriv (fun _ : ℂ ↦ (1 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))) s =
      b65p_exponent 0 * 1 - 1 * b65p_exponent 0 +
        (s - 0) • ((Ring.inverse (1 : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65p_regularPart (Fin 4 → ℂ) (fun _ : Fin 1 ↦ (0 : ℂ))
            (fun _ ↦ b65p_exponent 0) 0 s * 1) * 1) := by
  intro s _
  simp [b65p_regularPart]

/-- **Chain check toward `g32r_PeriodMap`.** The record supplies the fields `curve`,
`curve_cont` and `curve_zero` for any chart `V` containing the polydisc about the base point;
the other fields are explicit binders stated with that curve. This derives none of them. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p) (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (hsub : b6t_polydisc (b65p_curve p 0) ⊆ V)
    (period : (Fin 10 → ℂ) → Fin 9 → ℂ) (han : AnalyticOnNhd ℂ period V)
    (hmaps : MapsTo period V (g32m_Domain : Set (Fin 9 → ℂ)))
    (hisog : ∀ t (ht : t ∈ V), ∃ s, g32t_KIsog (P.fiber s) (F.univ ⟨period t, hmaps ht⟩))
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (hjet : g32r_CertifiedJet jet)
    (hcodiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ period (b65p_curve p θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    Nonempty (g32r_PeriodMap F P) :=
  ⟨{ V := V, isOpen_V := hV, period := period, analytic := han, mapsTo := hmaps,
     isog := hisog, curve := b65p_curve p, curve_cont := O.curve_cont,
     curve_zero := hsub O.curve_zero, jet := jet, jet_certified := hjet, codiff := hcodiff }⟩

/-- **Chain check.** The certified boxes give the two path fields, and the marked tuple of the
deformation lies in the selected column component (`b65b_component`). -/
example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ContinuousAt (b65p_curve p) 0 ∧ b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0) ∧
      b4_SameComponent b65s_columnRoot b65b_final :=
  let ⟨O⟩ := b65p_outputs p hp
  ⟨O.curve_cont, O.curve_zero, b65b_component⟩

end HodgeLean.Foundations.Program

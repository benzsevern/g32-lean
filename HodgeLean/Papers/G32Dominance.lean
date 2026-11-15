import HodgeLean.Papers.G32DominanceProofs

/-! # G32 Theorem A, stage 4: dominance (FROZEN SPEC)

Stage 4 of the premise-first route to G32 v0.16 Theorem A: the analytic open-image step, the link
from the exported rank certificate to "rank nine near the base point" for any analytic matrix with
the certified jet, the named premise `g32r_PeriodMap` for the geometric content (FGP's
codifferential formula, the Schlesinger deformation and the period map of the Hurwitz family),
and the bridge `g32r_dominant` to the field `dominant` of `g32h_RemainingFields F P`.

Claimed:
* a map from a finite-dimensional complex normed space to `ℂ⁹` with a strict derivative of rank
  nine at `x` sends every open neighbourhood of `x` onto a set containing an open neighbourhood of
  the image point; in particular for an analytic map on an open set (the holomorphic submersion
  step, from Mathlib's inverse function theorem);
* the rank of `L A R` for invertible `L`, `R` is the rank of `A`, read off as the `finrank` of the
  range of a linear map;
* for every analytic `9 × 10` matrix `M(θ)` whose Taylor coefficients of order at most seven are
  the exported rational jets (`g32r_CertifiedJet`): `rk M(0) = 5`, and `rk M(θ) = 9` for every
  `θ ≠ 0` near `0` (from `papers_g32_rank_constant` and `papers_g32_powerSeries_order_complex`);
* the implication from a period map `Φ : g32r_PeriodMap F P` to a parameter point where the
  derivative of the period map has rank nine, and to the exact `dominant` field over `F` and `P`.

Not claimed: that the exported matrix is the codifferential of the geometric period map (FGP's
formula, G32 Lemmas 5.1, 5.3 and 5.8, and the Schlesinger identification are the premise
`g32r_PeriodMap`); any period map, variation of Hodge structure, Hurwitz space or isomonodromic
deformation; the rank-nine locus being Zariski open; any algebraicity, discriminant, spreading or
transport (stages 3, 5 and 6). No period map is constructed, so Theorem A itself remains
unasserted.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set Filter
open scoped Topology
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

section Analytic

/-- **The open-image step.** Let `f : E → ℂ⁹` have a strict derivative `f'` at `x` whose range has
dimension nine, i.e. `f'` is onto. Then for every open `V ∋ x` the image `f '' V` contains an open
neighbourhood of `f x`. (A rank-nine derivative forces `dim E ≥ 9`.)
Source: G32 v0.16, Lemma 5.1 ("the period map is a submersion at `C₁`") and the first paragraph of
the proof of Theorem 7.2 ("`Φ(Δ)` contains a ball"); the surjective inverse function theorem,
Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_surj`. -/
theorem g32r_open_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (f : E → Fin 9 → ℂ) (f' : E →L[ℂ] Fin 9 → ℂ) (x : E) (V : Set E)
    (hV : IsOpen V) (hx : x ∈ V) (hf : HasStrictFDerivAt f f' x)
    (hrank : Module.finrank ℂ (LinearMap.range (f' : E →ₗ[ℂ] Fin 9 → ℂ)) = 9) :
    ∃ U : Set (Fin 9 → ℂ), IsOpen U ∧ f x ∈ U ∧ U ⊆ f '' V :=
  g32r_open_image_aux f f' x V hV hx hf hrank

/-- The image contains a nonempty open set. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (f : E → Fin 9 → ℂ) (f' : E →L[ℂ] Fin 9 → ℂ) (x : E) (V : Set E) (hV : IsOpen V)
    (hx : x ∈ V) (hf : HasStrictFDerivAt f f' x)
    (hrank : Module.finrank ℂ (LinearMap.range (f' : E →ₗ[ℂ] Fin 9 → ℂ)) = 9) :
    ∃ U : Set (Fin 9 → ℂ), IsOpen U ∧ U.Nonempty ∧ U ⊆ f '' V :=
  let ⟨U, hU, hxU, hUV⟩ := g32r_open_image f f' x V hV hx hf hrank
  ⟨U, hU, ⟨f x, hxU⟩, hUV⟩

/-- **The open-image step for an analytic map.** An analytic map `f` on an open set `V` of a
finite-dimensional complex space, with values in `ℂ⁹`, whose derivative at `x ∈ V` has rank nine,
has image `f '' V` containing an open neighbourhood of `f x`.
Source: G32 v0.16, Lemma 5.1 and the proof of Theorem 7.2; Mathlib's
`AnalyticAt.hasStrictFDerivAt` and `HasStrictFDerivAt.map_nhds_eq_of_surj`. -/
theorem g32r_open_image_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (f : E → Fin 9 → ℂ) (V : Set E) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f V) (x : E) (hx : x ∈ V)
    (hrank : Module.finrank ℂ (LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin 9 → ℂ)) = 9) :
    ∃ U : Set (Fin 9 → ℂ), IsOpen U ∧ f x ∈ U ∧ U ⊆ f '' V :=
  g32r_open_image_analytic_aux f V hV hf x hx hrank

/-- The image of the open set is a neighbourhood of `f x`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (f : E → Fin 9 → ℂ) (V : Set E) (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V) (x : E)
    (hx : x ∈ V)
    (hrank : Module.finrank ℂ (LinearMap.range (fderiv ℂ f x : E →ₗ[ℂ] Fin 9 → ℂ)) = 9) :
    f '' V ∈ 𝓝 (f x) :=
  let ⟨_, hU, hxU, hUV⟩ := g32r_open_image_analytic f V hV hf x hx hrank
  Filter.mem_of_superset (hU.mem_nhds hxU) hUV

end Analytic

section Certificate

/-- **Rank is invariant under changes of bases.** If `A = L · [f] · R` with `L`, `R` invertible
and `[f]` the standard matrix of a linear map `f : ℂ¹⁰ → ℂ⁹`, then `rk A = dim (range f)`. This
is how the matrix `𝐌(θ)` in the bases `(r_a)`, `(q_b)` and numerator coordinates gives the rank of
the derivative of the period map in coordinates.
Source: G32 v0.16, Remark 5.10 (analytic changes of bases multiply `𝐌(θ)` on both sides by
invertible matrices); Mathlib's `Matrix.rank_mul_eq_left_of_isUnit_det` and
`Matrix.rank_mul_eq_right_of_isUnit_det`. -/
theorem g32r_rank_conj (A : Matrix (Fin 9) (Fin 10) ℂ)
    (f : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) (L : Matrix (Fin 9) (Fin 9) ℂ)
    (R : Matrix (Fin 10) (Fin 10) ℂ) (hL : IsUnit L) (hR : IsUnit R)
    (h : A = L * LinearMap.toMatrix' f * R) :
    A.rank = Module.finrank ℂ (LinearMap.range f) :=
  g32r_rank_conj_aux A f L R hL hR h

example (f : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) :
    (LinearMap.toMatrix' f).rank = Module.finrank ℂ (LinearMap.range f) :=
  g32r_rank_conj _ f 1 1 isUnit_one isUnit_one (by simp)

/-- **A certified jet has rank five at `θ = 0`.** Its value at `0` is the exported constant jet
`papers8_M0`, of rank five (`papers_g32_rank_constant`); so the base cover `C₀` alone does not give
rank nine.
Source: G32 v0.16, Proposition 5.9 (1) (`rk 𝐌(0) = rk μ_{C₀} = 5`) and Remark 5.12. -/
theorem g32r_jet_rank_zero (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (hM : g32r_CertifiedJet M) :
    (M 0).rank = 5 :=
  g32r_jet_rank_zero_aux M hM

example (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (hM : g32r_CertifiedJet M) : (M 0).rank ≠ 9 := by
  rw [g32r_jet_rank_zero M hM]; decide

/-- **A certified jet has rank nine at every small `θ ≠ 0`.** The minor of `M(θ)` omitting the
column of `s⁰` is analytic at `0`, and its Taylor coefficients of order at most seven are those of
the determinant of any matching power-series matrix, which has order seven
(`papers_g32_powerSeries_order_complex`); so the minor has an isolated zero at `0` and `M(θ)` has
a nonsingular `9 × 9` minor for `θ ≠ 0` near `0`.
Source: G32 v0.16, Proposition 5.9 (2) and (3) and the appendix "The rank certificate". -/
theorem g32r_jet_rank_nine (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (hM : g32r_CertifiedJet M) :
    ∀ᶠ θ in 𝓝[≠] (0 : ℂ), (M θ).rank = 9 :=
  g32r_jet_rank_nine_aux M hM

/-- Rank nine at some point. -/
example (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (hM : g32r_CertifiedJet M) :
    ∃ θ, θ ≠ 0 ∧ (M θ).rank = 9 :=
  ((g32r_jet_rank_nine M hM).and self_mem_nhdsWithin).exists.imp fun _ h => ⟨h.2, h.1⟩

end Certificate

section Bridge

/-- **The period map has rank nine at some parameter point.** For `θ ≠ 0` near `0`, `C_θ` lies in
the chart, the jet is the derivative of the period map at `C_θ` up to changes of bases (`codiff`),
and the jet has rank nine (`g32r_jet_rank_nine`, `g32r_rank_conj`).
Source: G32 v0.16, Corollary 5.11 (the period map is a submersion at `C_θ` for small `θ ≠ 0`),
from Lemma 5.1 and Proposition 5.9. -/
theorem g32r_period_rank_nine (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (Φ : g32r_PeriodMap F P) :
    ∃ t ∈ Φ.V, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ Φ.period t : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ)) = 9 :=
  g32r_period_rank_nine_aux F P Φ

example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (Φ : g32r_PeriodMap F P) :
    ∃ t ∈ Φ.V, Φ.period t ∈ (g32m_Domain : Set (Fin 9 → ℂ)) :=
  let ⟨t, ht, _⟩ := g32r_period_rank_nine F P Φ
  ⟨t, ht, Φ.mapsTo ht⟩

/-- **Dominance, the bridge to the stage field.** From a period map `Φ`, a nonempty open
`U ⊆ 𝓗₃` each of whose points is the target of a `K`-linear polarized isogeny from some fibre of
`P`: the exact type of the field `dominant` of `g32h_RemainingFields F P` (and of
`g32m_StageFields`). The open set is the preimage in `𝓗₃` of the open set of
`g32r_open_image_analytic`, at the point of `g32r_period_rank_nine`.
Source: G32 v0.16, Corollary 5.11 and the first paragraph of the proof of Theorem 7.2 ("`Φ(Δ)`
contains a ball `𝓑`" and the isogeny `N₁ m : A_ρ(C) → A_z`). -/
theorem g32r_dominant (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (Φ : g32r_PeriodMap F P) :
    ∃ U : Set g32m_Domain, IsOpen U ∧ U.Nonempty ∧
      ∀ m ∈ U, ∃ s, g32t_KIsog (P.fiber s) (F.univ m) :=
  g32r_dominant_aux F P Φ

/-- The bridge fills the field `dominant` of the remaining stage fields. -/
example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (Φ : g32r_PeriodMap F P)
    (fd : ∀ s (h : g32t_PolarizedWeil (P.fiber s)), g32t_disc h = classNegTwo)
    (fa : ∀ s, g32t_WeilAlg (P.fiber s))
    (sp : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (tr : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    g32h_RemainingFields F P :=
  ⟨fd, fa, g32r_dominant F P Φ, sp, tr⟩

end Bridge

end HodgeLean.Papers

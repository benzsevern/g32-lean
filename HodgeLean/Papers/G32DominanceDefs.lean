import HodgeLean.Papers.G32FamilyDefs
import HodgeLean.Papers.PapersG32RankDefs

/-! # G32 Theorem A, stage 4: dominance (definitions)

Stage 4 of the premise-first route to G32 v0.16 Theorem A supplies the field `dominant` of
`g32h_RemainingFields F P`: a nonempty open `U ⊆ 𝓗₃` each of whose points is a `K`-isogeny target
of some fibre of the Prym family. This file records:

* `g32r_CertifiedJet`: a complex-analytic `9 × 10` matrix-valued function of `θ` near `0` whose
  Taylor coefficients of order at most seven are the exported rational jets `papers8_Mseries` of
  the rank certificate (G32 Proposition 5.9 and the appendix "The rank certificate");
* `g32r_PeriodMap`: the named premise holding a local analytic period map from a parameter
  neighbourhood of the Hurwitz family to `𝓗₃` (`g32m_Domain`), its fibre-to-isogeny-class
  property, and the identification of its derivative along the Schlesinger curve with a certified
  jet (FGP's codifferential formula, G32 Lemma 5.1 and Lemma 5.8).

Nothing here asserts dominance, an open image, a rank, algebraicity, a discriminant, spreading or
transport. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set Filter
open scoped Topology
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **A certified jet**: a function `M : ℂ → M_{9×10}(ℂ)` each of whose entries has a power
series expansion at `θ = 0`, with Taylor coefficients of order `k ≤ 7` equal to the complex image
of the rational coefficients `papers8_Mseries` exported by the rank certificate. In the paper `M`
is the matrix `𝐌(θ)` of `μ_{C_θ}` in the bases `(r_a)`, `(q_b)` and in numerator coordinates
(Subsection 5.5, item (7)), analytic by Lemma 5.8; this definition records only the analytic and
numerical shape, not that identification.
Source: G32 v0.16, Lemma 5.8 (Jets), Proposition 5.9 and the appendix "The rank certificate";
the exported data `papers8_M0`, …, `papers8_M7`. -/
def g32r_CertifiedJet (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ) : Prop :=
  ∃ p : Fin 9 → Fin 10 → FormalMultilinearSeries ℂ ℂ ℂ,
    (∀ i j, HasFPowerSeriesAt (fun θ => M θ i j) (p i j) 0) ∧
      ∀ i j k, k ≤ 7 →
        (p i j).coeff k = algebraMap ℚ ℂ (PowerSeries.coeff k (papers8_Mseries i j))

/-- Unfolding the definition. -/
example (M : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (h : g32r_CertifiedJet M) :
    ∃ p : Fin 9 → Fin 10 → FormalMultilinearSeries ℂ ℂ ℂ,
      ∀ i j, HasFPowerSeriesAt (fun θ => M θ i j) (p i j) 0 :=
  let ⟨p, hp, _⟩ := h
  ⟨p, hp⟩

/-- **The local period map of the Hurwitz family (premise).** Over a Prym family `P` and a
universal family `F`:

* `V`: an open set of `ℂ¹⁰`, a chart of the configuration space of thirteen branch points modulo
  `PGL₂` near the base cover `C₀` (over which the covers `C ∈ Hur°` form an analytic family);
* `period`: an analytic map on `V` with values in `𝓗₃` (`mapsTo`): the complex structure of
  `H₁(A_ρ(C), ℝ)` transported by a Landherr marking `m`, in the coordinates of `g32m_Domain`;
* `isog`: each parameter value `t ∈ V` is a cover whose factor `A_ρ(C_t)` is a fibre `P.fiber s`
  with a `K`-linear polarized isogeny onto the universal fibre at `period t` (the map
  `N₁ m` of the proof of G32 Theorem 7.2);
* `curve`: the Schlesinger path `θ ↦ C_θ` in the chart, continuous at `0`, with `C₀ ∈ V`;
* `jet`, `jet_certified`: the matrix `𝐌(θ)` of the codifferential along the path, a certified jet;
* `codiff`: for `θ` near `0`, `𝐌(θ)` is the matrix of the derivative of `period` at `C_θ` up to
  invertible changes of bases on both sides (FGP's formula: the codifferential of the period map
  is multiplication of differentials, and `𝐌(θ)` is its matrix in the bases `(r_a ⊗ q_b)` of the
  cotangent space of `𝓗₃` and the numerator coordinates of the cotangent space of `Hur°`; the
  transpose and the choice of coordinates are absorbed into `L` and `R`).

No field states an open image, a rank, dominance, algebraicity, a discriminant, spreading or
transport. The rank nine comes from the certificate and the open image from the inverse function
theorem, both in Lean (the frozen statements `g32r_jet_rank_nine` and `g32r_open_image_analytic`).
The repository has no variations of Hodge structure, period maps of families of abelian varieties,
Hurwitz spaces or isomonodromic deformations, so their outputs are recorded here as fields. This
structure is a premise; nothing derives it.
Source: Frediani–Ghigi–Penegini, *Shimura varieties in the Torelli locus via Galois coverings*,
IMRN 2015, §§2–3 (the codifferential of the period map as multiplication of differentials);
G32 v0.16, §5: Lemma 5.1 (Codifferential), Subsection 5.2 (the rigid starting system), Lemma 5.6
(Schlesinger), Subsection 5.5 and Lemma 5.8 (Jets), and the first paragraph of the proof of
Theorem 7.2 (the period map `Φ : Δ → 𝓗₃` and the isogeny `N₁ m`); Katz, *Rigid Local Systems*,
Ann. of Math. Stud. 139 (1996), Theorem 1.1.2 (the starting system). -/
structure g32r_PeriodMap (F : g32m_UniversalFamily) (P : g32h_PrymFamily) where
  /-- The parameter chart. -/
  V : Set (Fin 10 → ℂ)
  /-- The chart is open. -/
  isOpen_V : IsOpen V
  /-- The period map in coordinates. -/
  period : (Fin 10 → ℂ) → Fin 9 → ℂ
  /-- The period map is analytic on the chart. -/
  analytic : AnalyticOnNhd ℂ period V
  /-- The period map lands in `𝓗₃`. -/
  mapsTo : MapsTo period V (g32m_Domain : Set (Fin 9 → ℂ))
  /-- Each parameter value is a fibre isogenous to the universal fibre at its period. -/
  isog : ∀ t (ht : t ∈ V), ∃ s, g32t_KIsog (P.fiber s) (F.univ ⟨period t, mapsTo ht⟩)
  /-- The Schlesinger path `θ ↦ C_θ`. -/
  curve : ℂ → Fin 10 → ℂ
  /-- The path is continuous at `0`. -/
  curve_cont : ContinuousAt curve 0
  /-- The base cover lies in the chart. -/
  curve_zero : curve 0 ∈ V
  /-- The matrix of the codifferential along the path. -/
  jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ
  /-- Its Taylor coefficients are the exported ones. -/
  jet_certified : g32r_CertifiedJet jet
  /-- FGP: near `0`, the jet is the derivative of the period map up to changes of bases. -/
  codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ, ∃ R : Matrix (Fin 10) (Fin 10) ℂ,
    IsUnit L ∧ IsUnit R ∧
      jet θ = L * LinearMap.toMatrix'
        (fderiv ℂ period (curve θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R

/-- A period map has a nonempty chart. -/
example (F : g32m_UniversalFamily) (P : g32h_PrymFamily) (Φ : g32r_PeriodMap F P) :
    Φ.V.Nonempty :=
  ⟨Φ.curve 0, Φ.curve_zero⟩

end HodgeLean.Papers

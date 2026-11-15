import HodgeLean.Foundations.QuotientDuality.ProperCycleTriangulationDimension
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Actual complex chart dimensions bound geometric triangulation faces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual complex chart at a point of an intrinsic face bounds that face by twice the complex chart dimension.
Source: Hatcher, Algebraic Topology, section 2.2, local homology and dimension;
Munkres, Elements of Algebraic Topology, section 2, geometric complexes.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_card_le_of_complex_chart {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (X : TopCat.{0}) (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) (e : K.space ≃ₜ X)
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (d : ℕ) (φ : OpenPartialHomeomorph X (Fin d → ℂ)) (hφ : e x ∈ φ.source) :
    s.card ≤ 2 * d + 1 := by
  letI : T1Space X := e.t1Space
  let c := localClassOfChart d φ (e x) hφ
  have hc : c ≠ 0 := localClassOfChart_ne_zero d φ (e x) hφ
  let H := properCycle_local_homology_homeomorph_iso
    (X := TopCat.of K.space) (Y := X) e x (2 * d)
  have hsource : H.inv c ≠ 0 := by
    intro hz
    have hh := congrArg H.hom hz
    rw [H.inv_hom_id_apply, map_zero] at hh
    exact hc hh
  exact properCycle_geometric_face_card_le_of_local_ne_zero K hK V hV s hs x hx (2 * d)
    (H.inv c) hsource

/-- Actual complex charts meeting intrinsic face interiors supply a uniform triangulation face bound.
Source: Hatcher, Algebraic Topology, section 2.2; Munkres, Elements of Algebraic Topology, section 2.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_card_bound_of_complex_chart_family {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (X : TopCat.{0}) (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) (e : K.space ≃ₜ X) (d : ℕ)
    (hcharts : ∀ s ∈ K.faces, ∃ (x : K.space),
      x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      ∃ (m : ℕ) (φ : OpenPartialHomeomorph X (Fin m → ℂ)), m ≤ d ∧ e x ∈ φ.source) :
    ∀ s ∈ K.faces, s.card ≤ 2 * d + 1 := by
  intro s hs
  obtain ⟨x, hx, m, φ, hm, hφ⟩ := hcharts s hs
  have h := properCycle_face_card_le_of_complex_chart X K hK V hV e s hs x hx m φ hφ
  omega

/-- Charts on actual triangulated stratum closures bound every face of the selected marked subcomplex.
Source: Hatcher, Algebraic Topology, section 2.2; Bredon, Sheaf Theory, second edition, V.9,
finite stratification and local dimension.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_face_card_bound_of_charted_pieces {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V) (d : ℕ)
    (hpieces : ∀ s ∈ D.faces,
      ∃ (L : Geometry.SimplicialComplex ℝ E), L.faces ⊆ K.faces ∧ s ∈ L.faces ∧
        ∃ (X : TopCat.{0}) (e : L.space ≃ₜ X) (x : L.space),
          x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
          ∃ (m : ℕ) (φ : OpenPartialHomeomorph X (Fin m → ℂ)), m ≤ d ∧ e x ∈ φ.source) :
    ∀ s ∈ D.faces, s.card ≤ 2 * d + 1 := by
  intro s hs
  obtain ⟨L, hLK, hsL, X, e, x, hx, m, φ, hm, hφ⟩ := hpieces s hs
  have hL : L.faces.Finite := hK.subset hLK
  have hLV : ∀ a ∈ L.vertices, a ∈ V := by
    intro a ha
    exact hV a (hLK ha)
  have h := properCycle_face_card_le_of_complex_chart X L hL V hLV e s hsL x hx m φ hφ
  omega

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricHomologyDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleLabeledCarrier

/-! # Ordinary homology dimension of actual finite geometric complexes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual finite geometric complex has zero ordinary rational homology above the cardinal dimension of its original faces.
Source: Hatcher, Algebraic Topology, sections 2.1 and 4G; Munkres, Elements of Algebraic Topology, section 2.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_complex_homology_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (d : ℕ) (hbound : ∀ s ∈ K.faces, s.card ≤ d + 1) (n : ℕ) (hn : d < n) :
    Subsingleton (Homology ℚ (TopCat.of K.space) n) := by
  classical
  obtain ⟨e0, _, _⟩ := properCycle_finite_complex_weight_coordinates K hK V hV
  let F : Set (Finset V) := {t | ∃ s ∈ K.faces, t = Finset.univ.filter (fun a => a.val ∈ s)}
  have hF : ∀ t ∈ F, t.card ≤ d + 1 := by
    rintro t ⟨s, hs, rfl⟩
    have hc : (Finset.univ.filter (fun a : V => a.val ∈ s)).card ≤ s.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro a ha
        exact (Finset.mem_filter.mp ha).2
      · intro a _ b _ hab
        exact Subtype.ext hab
    exact hc.trans (hbound s hs)
  let e := e0.trans (properCycle_labeled_carrier_homeomorph K.faces (fun a : V => a.val))
  exact properCycle_homeomorph_homology_subsingleton
    (X := TopCat.of K.space)
    (Y := TopCat.of {u : stdSimplex ℝ V | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0}) e n
    (properCycle_barycentric_carrier_homology_vanishes F d hF n hn)

end HodgeLean.Foundations.QuotientDuality

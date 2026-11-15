import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVSequence

/-! # Actual quotient-sequence morphisms under subcomplex refinement
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Refining the two specified subcomplexes gives an actual morphism of their original signed quotient sequences.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_subcomplex_quotient_map_comp.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_refinement
    {K : SSet.{0}} {P Q P' Q' : K.Subcomplex} (hP : P ≤ P') (hQ : Q ≤ Q') :
    properCycle_subcomplex_quotient_sequence P Q ⟶
      properCycle_subcomplex_quotient_sequence P' Q' := by
  refine ShortComplex.homMk
    (properCycle_subcomplex_quotient_map (inf_le_inf hP hQ))
    (biprod.map (properCycle_subcomplex_quotient_map hP) (properCycle_subcomplex_quotient_map hQ))
    (properCycle_subcomplex_quotient_map (sup_le_sup hP hQ)) ?_ ?_
  · apply biprod.hom_ext
    · simp only [properCycle_subcomplex_quotient_sequence, Category.assoc,
        biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      rw [properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp]
    · simp only [properCycle_subcomplex_quotient_sequence, Category.assoc,
        biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      rw [properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp]
  · apply biprod.hom_ext'
    · simp only [properCycle_subcomplex_quotient_sequence, biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      rw [properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp]
    · simp only [properCycle_subcomplex_quotient_sequence, biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
      rw [properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp]

/-- The original connecting maps commute with the literal quotient refinement maps on both terms.
Source: Mathlib, Algebra/Homology/HomologySequence.lean, δ_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_subcomplex_mv_refinement_connecting
    (X : TopCat.{0}) {P Q P' Q' : (TopCat.toSSet.obj X).Subcomplex}
    (hP : P ≤ P') (hQ : Q ≤ Q') (n : ℕ) :
    (properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (n+1) n rfl ≫
        HomologicalComplex.homologyMap
          (properCycle_subcomplex_quotient_map (inf_le_inf hP hQ)) n =
      HomologicalComplex.homologyMap
          (properCycle_subcomplex_quotient_map (sup_le_sup hP hQ)) (n+1) ≫
        (properCycle_subcomplex_quotient_sequence_shortExact X P' Q').δ (n+1) n rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (properCycle_subcomplex_mv_refinement hP hQ)
    (properCycle_subcomplex_quotient_sequence_shortExact X P Q)
    (properCycle_subcomplex_quotient_sequence_shortExact X P' Q') (n+1) n rfl

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexQuotientFunctoriality
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVSequence

/-! # Actual signed quotient sequences under ambient simplicial transport
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A simplicial map preserving both original subcomplexes induces an actual morphism of their signed relative quotient sequences.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_subcomplex_quotient_morphism_inclusion.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_morphism
    {K L : SSet.{0}} (f : K ⟶ L) (P Q : K.Subcomplex) (P' Q' : L.Subcomplex)
    (hP : P ≤ P'.preimage f) (hQ : Q ≤ Q'.preimage f) :
    properCycle_subcomplex_quotient_sequence P Q ⟶ properCycle_subcomplex_quotient_sequence P' Q' := by
  refine ShortComplex.homMk
    (properCycle_subcomplex_quotient_morphism f (P ⊓ Q) (P' ⊓ Q') (inf_le_inf hP hQ))
    (biprod.map (properCycle_subcomplex_quotient_morphism f P P' hP)
      (properCycle_subcomplex_quotient_morphism f Q Q' hQ))
    (properCycle_subcomplex_quotient_morphism f (P ⊔ Q) (P' ⊔ Q') (sup_le_sup hP hQ)) ?_ ?_
  · apply biprod.hom_ext
    · simp only [properCycle_subcomplex_quotient_sequence, Category.assoc,
        biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact (properCycle_subcomplex_quotient_morphism_inclusion f
        inf_le_left inf_le_left (inf_le_inf hP hQ) hP).symm
    · simp only [properCycle_subcomplex_quotient_sequence, Category.assoc,
        biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (properCycle_subcomplex_quotient_morphism_inclusion f
        inf_le_right inf_le_right (inf_le_inf hP hQ) hQ).symm
  · apply biprod.hom_ext'
    · simp only [properCycle_subcomplex_quotient_sequence,
        biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact (properCycle_subcomplex_quotient_morphism_inclusion f
        le_sup_left le_sup_left hP (sup_le_sup hP hQ)).symm
    · simp only [properCycle_subcomplex_quotient_sequence,
        biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
      exact (properCycle_subcomplex_quotient_morphism_inclusion f
        le_sup_right le_sup_right hQ (sup_le_sup hP hQ)).symm

/-- The original signed connecting maps are natural under actual ambient simplicial transport preserving both specified subcomplexes.
Source: Mathlib, Algebra/Homology/HomologySequence.lean, δ_naturality; properCycle_subcomplex_mv_morphism.
HC no distance; AV milestone no distance. -/
theorem properCycle_subcomplex_mv_morphism_connecting
    (X Y : TopCat.{0}) (f : TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj Y)
    (P Q : (TopCat.toSSet.obj X).Subcomplex) (P' Q' : (TopCat.toSSet.obj Y).Subcomplex)
    (hP : P ≤ P'.preimage f) (hQ : Q ≤ Q'.preimage f) (n : ℕ) :
    (properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (n+1) n rfl ≫
        HomologicalComplex.homologyMap
          (properCycle_subcomplex_mv_morphism f P Q P' Q' hP hQ).τ₁ n =
      HomologicalComplex.homologyMap
          (properCycle_subcomplex_mv_morphism f P Q P' Q' hP hQ).τ₃ (n+1) ≫
        (properCycle_subcomplex_quotient_sequence_shortExact Y P' Q').δ (n+1) n rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (properCycle_subcomplex_mv_morphism f P Q P' Q' hP hQ)
    (properCycle_subcomplex_quotient_sequence_shortExact X P Q)
    (properCycle_subcomplex_quotient_sequence_shortExact Y P' Q') (n+1) n rfl

end HodgeLean.Foundations.QuotientDuality

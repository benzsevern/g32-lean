import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVSequence
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexCapNaturality

/-! # Actual relative Mayer--Vietoris with a fixed first subcomplex -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal signed quotient sequence modulo the same fixed first subcomplex in each term.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris with fixed subspace.
HC no distance; AV milestone no distance. -/
def properCycle_fixed_subcomplex_sequence
    {K : SSet.{0}} (A P Q : K.Subcomplex) : ShortComplex (ChainCategory ℚ) :=
  ShortComplex.mk
    (biprod.lift
      (properCycle_subcomplex_quotient_map (sup_le_sup_left (inf_le_left : P ⊓ Q ≤ P) A))
      (-properCycle_subcomplex_quotient_map (sup_le_sup_left (inf_le_right : P ⊓ Q ≤ Q) A)))
    (biprod.desc
      (properCycle_subcomplex_quotient_map (sup_le_sup_left (le_sup_left : P ≤ P ⊔ Q) A))
      (properCycle_subcomplex_quotient_map (sup_le_sup_left (le_sup_right : Q ≤ P ⊔ Q) A))) (by
        rw [biprod.lift_desc, Preadditive.neg_comp,
          properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp]
        exact add_neg_cancel _)

/-- The literal relative sequence with fixed first subcomplex is canonically the original union-subcomplex sequence.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris and subcomplex distributivity.
HC no distance; AV milestone no distance. -/
def properCycle_fixed_subcomplex_sequence_iso
    {K : SSet.{0}} (A P Q : K.Subcomplex) :
    properCycle_subcomplex_quotient_sequence (A ⊔ P) (A ⊔ Q) ≅
      properCycle_fixed_subcomplex_sequence A P Q := by
  have hI : (A ⊔ P) ⊓ (A ⊔ Q) = A ⊔ (P ⊓ Q) := properCycle_subcomplex_sup_inf A P Q
  have hU : (A ⊔ P) ⊔ (A ⊔ Q) = A ⊔ (P ⊔ Q) := by
    simp only [sup_assoc, sup_left_comm, sup_left_idem]
  refine ShortComplex.isoMk (properCycle_subcomplex_quotient_iso_of_eq hI)
    (Iso.refl _) (properCycle_subcomplex_quotient_iso_of_eq hU) ?_ ?_
  · change properCycle_subcomplex_quotient_map hI.le ≫ biprod.lift _ _ =
      biprod.lift _ _ ≫ 𝟙 _
    erw [Category.comp_id]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst]
      rw [properCycle_subcomplex_quotient_map_comp]
    · simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_neg]
      rw [properCycle_subcomplex_quotient_map_comp]
  · change 𝟙 _ ≫ biprod.desc _ _ = biprod.desc _ _ ≫ properCycle_subcomplex_quotient_map hU.le
    erw [Category.id_comp]
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc, biprod.inl_desc_assoc]
      rw [properCycle_subcomplex_quotient_map_comp]
    · simp only [biprod.inr_desc, biprod.inr_desc_assoc]
      rw [properCycle_subcomplex_quotient_map_comp]

/-- The original relative Mayer--Vietoris sequence with a fixed first subcomplex is short exact.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_fixed_subcomplex_sequence_shortExact
    (X : TopCat.{0}) (A P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (properCycle_fixed_subcomplex_sequence A P Q).ShortExact :=
  ShortComplex.shortExact_of_iso (properCycle_fixed_subcomplex_sequence_iso A P Q)
    (properCycle_subcomplex_quotient_sequence_shortExact X (A ⊔ P) (A ⊔ Q))

end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVModels

/-! # The original signed relative quotient sequence of simplicial subcomplexes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original quotient sequence uses the signed pair of intersection maps and addition of the union maps.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris chains.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_quotient_sequence
    {K : SSet.{0}} (P Q : K.Subcomplex) : ShortComplex (ChainCategory ℚ) :=
  ShortComplex.mk
    (biprod.lift (properCycle_subcomplex_quotient_map (inf_le_left : P ⊓ Q ≤ P))
      (-properCycle_subcomplex_quotient_map (inf_le_right : P ⊓ Q ≤ Q)))
    (biprod.desc (properCycle_subcomplex_quotient_map (le_sup_left : P ≤ P ⊔ Q))
      (properCycle_subcomplex_quotient_map (le_sup_right : Q ≤ P ⊔ Q))) (by
        rw [biprod.lift_desc, Preadditive.neg_comp,
          properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp]
        exact add_neg_cancel _)

/-- The original signed intersection map retains the two actual ambient quotient projections.
Source: Hatcher, Algebraic Topology, section 2.2, the relative Mayer--Vietoris diagonal.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_sequence_left_projection
    {K : SSet.{0}} (P Q : K.Subcomplex) :
    cokernel.π (SSet.chainComplexMap (P ⊓ Q).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_subcomplex_quotient_sequence P Q).f =
      biprod.lift (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)))
        (-cokernel.π (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ))) := by
  apply biprod.hom_ext
  · simp only [properCycle_subcomplex_quotient_sequence, Category.assoc, biprod.lift_fst]
    erw [biprod.lift_fst]
    exact properCycle_subcomplex_quotient_projection (inf_le_left : P ⊓ Q ≤ P)
  · simp only [properCycle_subcomplex_quotient_sequence, Category.assoc, biprod.lift_snd,
      Preadditive.comp_neg]
    erw [biprod.lift_snd]
    exact congrArg Neg.neg (properCycle_subcomplex_quotient_projection (inf_le_right : P ⊓ Q ≤ Q))

/-- The original union map adds the two literal ambient quotient projections.
Source: Hatcher, Algebraic Topology, section 2.2, the relative Mayer--Vietoris sum.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_sequence_right_projection
    {K : SSet.{0}} (P Q : K.Subcomplex) :
    biprod.map (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)))
        (cokernel.π (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ))) ≫
        (properCycle_subcomplex_quotient_sequence P Q).g =
      biprod.desc (cokernel.π (SSet.chainComplexMap (P ⊔ Q).ι (ModuleCat.of ℚ ℚ)))
        (cokernel.π (SSet.chainComplexMap (P ⊔ Q).ι (ModuleCat.of ℚ ℚ))) := by
  apply biprod.hom_ext'
  · simp only [properCycle_subcomplex_quotient_sequence, biprod.inl_map_assoc,
      biprod.inl_desc_assoc]
    erw [biprod.inl_desc, biprod.inl_desc]
    exact properCycle_subcomplex_quotient_projection (le_sup_left : P ≤ P ⊔ Q)
  · simp only [properCycle_subcomplex_quotient_sequence, biprod.inr_map_assoc,
      biprod.inr_desc_assoc]
    erw [biprod.inr_desc, biprod.inr_desc]
    exact properCycle_subcomplex_quotient_projection (le_sup_right : Q ≤ P ⊔ Q)

/-- The constructed subcomplex quotient diagram identifies the literal signed relative sequence with its original short exact model.
Source: Hatcher, Algebraic Topology, section 2.2, the relative chain sequence.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_sequence_iso
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    cokernel (properCycle_subcomplex_mv_to_ambient X P Q) ≅
      properCycle_subcomplex_quotient_sequence P Q := by
  let π := cokernel.π (properCycle_subcomplex_mv_to_ambient X P Q)
  letI : Epi π := by dsimp [π]; infer_instance
  refine ShortComplex.isoMk (properCycle_subcomplex_mv_left_iso X P Q)
    (properCycle_subcomplex_mv_middle_iso X P Q) (properCycle_subcomplex_mv_right_iso X P Q) ?_ ?_
  · letI : Epi π.τ₁ := by
      change Epi (ShortComplex.π₁.map π)
      infer_instance
    apply (cancel_epi π.τ₁).mp
    rw [← Category.assoc, properCycle_subcomplex_mv_left_projection,
      properCycle_subcomplex_sequence_left_projection]
    erw [π.comm₁₂_assoc, properCycle_subcomplex_mv_middle_projection]
    change biprod.lift _ _ = biprod.lift (𝟙 _) (-𝟙 _) ≫ biprod.map _ _
    apply biprod.hom_ext <;> simp
  · letI : Epi π.τ₂ := by
      change Epi (ShortComplex.π₂.map π)
      infer_instance
    apply (cancel_epi π.τ₂).mp
    rw [← Category.assoc, properCycle_subcomplex_mv_middle_projection,
      properCycle_subcomplex_sequence_right_projection]
    erw [π.comm₂₃_assoc, properCycle_subcomplex_mv_right_projection]
    change biprod.desc _ _ = biprod.desc (𝟙 _) (𝟙 _) ≫ _
    apply biprod.hom_ext' <;> simp

/-- The literal signed sequence of actual relative subcomplex chain quotients is short exact.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_quotient_sequence_shortExact
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (properCycle_subcomplex_quotient_sequence P Q).ShortExact :=
  ShortComplex.shortExact_of_iso (properCycle_subcomplex_mv_sequence_iso X P Q)
    (properCycle_subcomplex_relative_mv_shortExact X P Q)

end HodgeLean.Foundations.QuotientDuality

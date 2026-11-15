import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeMV

/-! # Actual relative Mayer--Vietoris sequences for simplicial subcomplexes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual simplicial subcomplex Mayer--Vietoris sequence maps to the ambient diagonal sequence by its literal inclusions.
Source: Hatcher, Algebraic Topology, section 2.2, small-chain Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_mv_to_ambient
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    subcomplexMayerVietorisShortComplex P Q ⟶ ProperCycleRelativeMV.ambientDiagonalShortComplex X := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  refine ShortComplex.homMk
    (C.map (P ⊓ Q).ι) (biprod.map (C.map P.ι) (C.map Q.ι)) (C.map (P ⊔ Q).ι) ?_ ?_
  · apply biprod.hom_ext
    · simp only [Category.assoc, ProperCycleRelativeMV.ambientDiagonalShortComplex,
        CommSq.shortComplex_f, biprod.lift_fst, subcomplexMayerVietorisShortComplex,
        biprod.map_fst, biprod.lift_fst_assoc, Category.comp_id]
      change C.map (P ⊓ Q).ι = C.map _ ≫ C.map _
      rw [← C.map_comp]
      rfl
    · simp only [Category.assoc, ProperCycleRelativeMV.ambientDiagonalShortComplex,
        CommSq.shortComplex_f, biprod.lift_snd, subcomplexMayerVietorisShortComplex,
        biprod.map_snd, biprod.lift_snd_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, Category.comp_id]
      congr 1
      change C.map (P ⊓ Q).ι = C.map _ ≫ C.map _
      rw [← C.map_comp]
      rfl
  · change biprod.map _ _ ≫ biprod.desc (𝟙 _) (𝟙 _) = _
    apply biprod.hom_ext'
    · simp only [subcomplexMayerVietorisShortComplex, CommSq.shortComplex_g,
        biprod.inl_map_assoc, biprod.inl_desc, Category.comp_id, biprod.inl_desc_assoc]
      change C.map P.ι = C.map _ ≫ C.map _
      rw [← C.map_comp]
      rfl
    · simp only [subcomplexMayerVietorisShortComplex, CommSq.shortComplex_g,
        biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id, biprod.inr_desc_assoc]
      change C.map Q.ι = C.map _ ≫ C.map _
      rw [← C.map_comp]
      rfl

/-- Quotienting the actual subcomplex Mayer--Vietoris diagram gives a short exact chain sequence.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_relative_mv_shortExact
    (X : TopCat.{0}) (P Q : (TopCat.toSSet.obj X).Subcomplex) :
    (cokernel (properCycle_subcomplex_mv_to_ambient X P Q)).ShortExact := by
  letI : Mono (properCycle_subcomplex_mv_to_ambient X P Q).τ₃ := by
    change Mono (SSet.chainComplexMap (P ⊔ Q).ι (ModuleCat.of ℚ ℚ))
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  exact ProperCycleRelativeMV.cokernel_shortExact_of_shortExact_of_mono_third
    (properCycle_subcomplex_mv_to_ambient X P Q)
    (subcomplexMayerVietorisShortComplex_shortExact P Q)
    (ProperCycleRelativeMV.ambientDiagonalShortComplex_shortExact X)

end HodgeLean.Foundations.QuotientDuality

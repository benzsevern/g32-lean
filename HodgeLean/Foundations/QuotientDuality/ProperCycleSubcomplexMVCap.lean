import HodgeLean.Foundations.QuotientDuality.ProperCycleFixedSubcomplexMV
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapConnecting

/-! # Actual cap morphisms of the relative subcomplex Mayer--Vietoris sequence -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original even quotient caps form an actual morphism from the fixed-relative Mayer--Vietoris degree tail to the original relative quotient sequence.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, cap products and relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
def properCycle_even_subcomplex_mv_cap_morphism
    {K : SSet.{0}} (A P Q : K.Subcomplex) (p : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    (properCycle_fixed_subcomplex_sequence A P Q).map
        ((properCycle_cap_tail_embedding p).restrictionFunctor (ModuleCat ℚ)) ⟶
      properCycle_subcomplex_quotient_sequence P Q := by
  let R := (properCycle_cap_tail_embedding p).restrictionFunctor (ModuleCat ℚ)
  letI : PreservesBinaryBiproducts R := preservesBinaryBiproducts_of_preservesBiproducts R
  let cI := properCycle_even_subcomplex_cap_chain_map A (P ⊓ Q) p hp φ hA hφ
  let cP := properCycle_even_subcomplex_cap_chain_map A P p hp φ hA hφ
  let cQ := properCycle_even_subcomplex_cap_chain_map A Q p hp φ hA hφ
  let cU := properCycle_even_subcomplex_cap_chain_map A (P ⊔ Q) p hp φ hA hφ
  let e := R.mapBiprod (properCycle_subcomplex_quotient (A ⊔ P)) (properCycle_subcomplex_quotient (A ⊔ Q))
  refine ShortComplex.homMk cI (e.hom ≫ biprod.map cP cQ) cU ?_ ?_
  · change cI ≫ biprod.lift _ _ = R.map (biprod.lift _ _) ≫ (e.hom ≫ biprod.map cP cQ)
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact properCycle_even_subcomplex_cap_inclusion A (P ⊓ Q) P inf_le_left p hp φ hA hφ
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp, Functor.map_neg]
      exact congrArg Neg.neg
        (properCycle_even_subcomplex_cap_inclusion A (P ⊓ Q) Q inf_le_right p hp φ hA hφ)
  · have hd : biprod.map cP cQ ≫
          (properCycle_subcomplex_quotient_sequence P Q).g =
        biprod.desc
          (R.map (properCycle_subcomplex_quotient_map (sup_le_sup_left (le_sup_left : P ≤ P ⊔ Q) A)))
          (R.map (properCycle_subcomplex_quotient_map (sup_le_sup_left (le_sup_right : Q ≤ P ⊔ Q) A))) ≫ cU := by
      apply biprod.hom_ext'
      · simp only [properCycle_subcomplex_quotient_sequence, biprod.inl_map_assoc,
          biprod.inl_desc_assoc]
        erw [biprod.inl_desc]
        exact properCycle_even_subcomplex_cap_inclusion A P (P ⊔ Q) le_sup_left p hp φ hA hφ
      · simp only [properCycle_subcomplex_quotient_sequence, biprod.inr_map_assoc,
          biprod.inr_desc_assoc]
        erw [biprod.inr_desc]
        exact properCycle_even_subcomplex_cap_inclusion A Q (P ⊔ Q) le_sup_right p hp φ hA hφ
    change (e.hom ≫ biprod.map cP cQ) ≫ (properCycle_subcomplex_quotient_sequence P Q).g =
      R.map (biprod.desc _ _) ≫ cU
    rw [Category.assoc]
    erw [hd]
    rw [← Category.assoc, biprod.mapBiprod_hom_desc]

end HodgeLean.Foundations.QuotientDuality

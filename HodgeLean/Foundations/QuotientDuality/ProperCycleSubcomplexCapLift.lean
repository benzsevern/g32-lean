import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexQuotient
import HodgeLean.Foundations.QuotientDuality.ProperCycleEvenCapChainMap

/-! # Actual cap descent through sums of simplicial subcomplexes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A cochain vanishing on the first subcomplex caps chains in its union with the second to zero in the actual quotient by the second.
Source: Hatcher, Algebraic Topology, section 3.3, cap descent through subspace chains.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_cap_subspace_zero
    {K : SSet.{0}} (A T : K.Subcomplex) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0) :
    (SSet.chainComplexMap (A ⊔ T).ι (ModuleCat.of ℚ ℚ)).f (p + q) ≫
        AlgebraicTopology.Simplicial.capHom ℚ p q φ ≫
          (cokernel.π (SSet.chainComplexMap T.ι (ModuleCat.of ℚ ℚ))).f q = 0 := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  let S := subcomplexMayerVietorisShortComplex A T
  have hsum : S.g ≫ C.map (A ⊔ T).ι = biprod.desc (C.map A.ι) (C.map T.ι) := by
    apply biprod.hom_ext'
    · simp only [S, subcomplexMayerVietorisShortComplex, CommSq.shortComplex_g,
        biprod.inl_desc_assoc, biprod.inl_desc]
      change C.map _ ≫ C.map _ = C.map _
      rw [← C.map_comp]
      rfl
    · simp only [S, subcomplexMayerVietorisShortComplex, CommSq.shortComplex_g,
        biprod.inr_desc_assoc, biprod.inr_desc]
      change C.map _ ≫ C.map _ = C.map _
      rw [← C.map_comp]
      rfl
  letI : Epi S.g := (subcomplexMayerVietorisShortComplex_shortExact A T).epi_g
  letI : Epi (S.g.f (p + q)) := inferInstance
  apply (cancel_epi (S.g.f (p + q))).mp
  rw [comp_zero, ← Category.assoc]
  have hsum' := congrArg (fun m => m.f (p + q)) hsum
  rw [HomologicalComplex.comp_f] at hsum'
  rw [hsum']
  apply HomologicalComplex.biprodX_ext_from
  · rw [← Category.assoc, HomologicalComplex.biprod_inl_desc_f]
    apply ModuleCat.hom_ext
    ext c
    change ((cokernel.π (C.map T.ι)).f q).hom
      (AlgebraicTopology.Simplicial.cap ℚ p q φ ((C.map A.ι).f (p + q) c)) = 0
    rw [← AlgebraicTopology.Simplicial.cap_naturality, hA]
    have hz := ConcreteCategory.congr_hom
      (AlgebraicTopology.Simplicial.capHom_zero (R := ℚ) (X := (A : SSet)) p q) c
    change AlgebraicTopology.Simplicial.cap ℚ p q (0 : AlgebraicTopology.Simplicial.Cochain ℚ A p) c = 0 at hz
    rw [hz, map_zero, map_zero]
  · rw [← Category.assoc, HomologicalComplex.biprod_inr_desc_f]
    apply ModuleCat.hom_ext
    ext c
    change ((cokernel.π (C.map T.ι)).f q).hom
      (AlgebraicTopology.Simplicial.cap ℚ p q φ ((C.map T.ι).f (p + q) c)) = 0
    rw [← AlgebraicTopology.Simplicial.cap_naturality]
    have hz := congrArg (fun m => m.f q) (cokernel.condition (C.map T.ι))
    exact ConcreteCategory.congr_hom hz _

end HodgeLean.Foundations.QuotientDuality

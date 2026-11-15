import HodgeLean.Foundations.QuotientDuality.ProperCycleCapTailZero

/-! # Original positive homology comparisons under degree-tail restriction -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original positive-degree homology comparison with a degree tail is natural for every actual chain map.
Source: Mathlib, Algebra/Homology/ShortComplex/HomologicalComplex.lean, natural three-term homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_homology_naturality
    {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap f (p + (q + 1)) ≫
        (properCycle_cap_tail_homology_iso L p q).hom =
      (properCycle_cap_tail_homology_iso K p q).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.restrictionMap f (properCycle_cap_tail_embedding p)) (q + 1) := by
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (p + (q + 1))).map f
  let G := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (q + 1)).map
    (HomologicalComplex.restrictionMap f (properCycle_cap_tail_embedding p))
  have h : ShortComplex.homologyMap (F ≫ (properCycle_cap_tail_sc_iso L p q).hom) =
      ShortComplex.homologyMap ((properCycle_cap_tail_sc_iso K p q).hom ≫ G) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    apply ModuleCat.hom_ext
    ext z
    rfl
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality

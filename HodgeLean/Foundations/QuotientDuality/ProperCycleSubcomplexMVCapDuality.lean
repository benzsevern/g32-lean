import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularMVComparison

/-! # Actual relative cap duality through the constructed connecting square -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The constructed relative Mayer--Vietoris cap square transports bijectivity from the intersection cap to the union cap when the actual middle homology groups vanish.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, the cap suspension argument.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_mv_cap_bijective
    (X : TopCat.{0}) (A P Q : (TopCat.toSSet.obj X).Subcomplex)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0)
    (hShi : IsZero ((properCycle_fixed_subcomplex_sequence A P Q).X₂.homology (p + (q + 1))))
    (hSlo : IsZero ((properCycle_fixed_subcomplex_sequence A P Q).X₂.homology (p + q)))
    (hThi : IsZero ((properCycle_subcomplex_quotient_sequence P Q).X₂.homology (q + 1)))
    (hTlo : IsZero ((properCycle_subcomplex_quotient_sequence P Q).X₂.homology q))
    (hc : Function.Bijective (properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ).hom) :
    Function.Bijective (properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q + 1) hp φ hA hφ).hom := by
  let eS := (properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δIso
    (p + (q + 1)) (p + q) (by change (p + q) + 1 = p + (q + 1); omega) hShi hSlo
  let eT := (properCycle_subcomplex_quotient_sequence_shortExact X P Q).δIso
    (q + 1) q (by simp) hThi hTlo
  have he : properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q + 1) hp φ hA hφ =
      eS.hom ≫ properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ ≫ eT.inv := by
    apply (cancel_mono eT.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact properCycle_subcomplex_mv_cap_connecting X A P Q p q hp φ hA hφ
  rw [he]
  exact eT.symm.toLinearEquiv.bijective.comp (hc.comp eS.toLinearEquiv.bijective)

end HodgeLean.Foundations.QuotientDuality

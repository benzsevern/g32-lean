import HodgeLean.Foundations.QuotientDuality.OrientationLinearDescent
import HodgeLean.Foundations.QuotientDuality.OrientationEquivariantComplex

/-! Absolute singular comparisons restricted to fixed homology classes. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma finite_quotient_chain_comparison_bijective
    (G : Type) [Group G] [Fintype G] (X Y : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] (q : X ⟶ Y)
    (hi : ∀ g, deckMap G X g ≫ q = q)
    (ρ : G →* End (SingularChainComplex ℚ X))
    (hρ : ∀ g, (ρ g).asHom = singularChainComplexMap ℚ (deckMap G X g⁻¹)) (i : ℕ)
    (hinj : Function.Injective (cohomologyMap ℚ i q))
    (hdescent : ∀ u : Cohomology ℚ X i,
      (∀ g, cohomologyMap ℚ i (deckMap G X g) u = u) →
        ∃ v, cohomologyMap ℚ i q v = u) :
    Function.Bijective (fun z :
      (complexHomologyRepresentation G (SingularChainComplex ℚ X) ρ i).invariants =>
        homologyMap ℚ i q z.1) := by
  have hfixed (z : (complexHomologyRepresentation G (SingularChainComplex ℚ X) ρ i).invariants)
      (g : G) : homologyMap ℚ i (deckMap G X g) z.1 = z.1 := by
    have h := z.2 g⁻¹
    change (HomologicalComplex.homologyMap (ρ g⁻¹).asHom i).hom z.1 = z.1 at h
    rw [hρ, inv_inv] at h
    exact h
  constructor
  · intro z w hzw
    change homologyMap ℚ i q z.1 = homologyMap ℚ i q w.1 at hzw
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply finite_quotient_homology_invariant_kernel G X i Y q hdescent (z.1 - w.1)
    · intro g
      rw [map_sub, hfixed z g, hfixed w g]
    · rw [map_sub, hzw, sub_self]
  · intro y
    obtain ⟨z, hz, hfix⟩ := finite_quotient_homology_fixed_lift G X Y q hi i
      (homology_surjective_of_cohomology_injective q i hinj) y
    refine ⟨⟨z, ?_⟩, hz⟩
    intro g
    change (HomologicalComplex.homologyMap (ρ g).asHom i).hom z = z
    rw [hρ]
    exact hfix g⁻¹

end HodgeLean.Foundations.QuotientDuality

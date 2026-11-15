import HodgeLean.Foundations.Program.SchoenTowerI1aChartGluing
import HodgeLean.Foundations.Program.SchoenTowerI1aPrincipalFactors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_chart_structure_factor
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X))
    (U : X.left.affineOpens) (hi : ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1) :
    ∃! v : Spec ↧(s2v_i1a_chartInvariants X G a U.1 hi) ⟶ Spec ↧ℂ,
      s2v_i1a_affineQuotientMap X G a U.1 hi ≫ v = U.1.ι ≫ X.hom := by
  apply s2v_i1ahi_affine_target_factor X G a U.1 U.2 hi _ _
  intro g
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, (a g).w]

/-- The complex structure maps of the actual invariant spectra form a cocone.
Source: SGA 1, Exposé V, §1, gluing invariant affine charts over the base. -/
def s2v_i1ahi_chartBaseCocone
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g) :
    Cocone (s2v_i1ahi_chartDiagram X G a) where
  pt := Spec ↧ℂ
  ι.app U := (s2v_i1ahi_chart_structure_factor X G a U.1 U.2).choose
  ι.naturality {U V} f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    letI := s2v_i1ahi_chart_epi X G a ha1 hamul U.1.1 U.1.2 U.2
    apply (cancel_epi (s2v_i1a_affineQuotientMap X G a U.1.1 U.2)).mp
    rw [← Category.assoc, s2v_i1ahi_chartDiagram_square, Category.assoc,
      (s2v_i1ahi_chart_structure_factor X G a V.1 V.2).choose_spec.1,
      ← Category.assoc, Scheme.homOfLE_ι,
      (s2v_i1ahi_chart_structure_factor X G a U.1 U.2).choose_spec.1]

example (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g) :
    (s2v_i1ahi_chartBaseCocone X G a ha1 hamul).pt = Spec ↧ℂ := rfl

lemma s2v_i1ahi_glued_complex_structure
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (c : Cocone (s2v_i1ahi_chartDiagram X G a)) (hc : IsColimit c) :
    ∃ s : c.pt ⟶ Spec ↧ℂ, ∀ U,
      s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫ c.ι.app U ≫ s = U.1.1.ι ≫ X.hom := by
  refine ⟨hc.desc (s2v_i1ahi_chartBaseCocone X G a ha1 hamul), fun U => ?_⟩
  rw [hc.fac]
  exact (s2v_i1ahi_chart_structure_factor X G a U.1 U.2).choose_spec.1

end HodgeLean.Foundations.Program

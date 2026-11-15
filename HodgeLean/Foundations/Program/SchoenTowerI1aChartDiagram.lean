import HodgeLean.Foundations.Program.SchoenTowerI1aChartTransitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The invariant spectra on invariant affine opens, with actual restriction transitions.
Source: SGA 1, Exposé V, §1, invariant affine quotient charts. -/
def s2v_i1ahi_chartDiagram
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X)) :
    {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1} ⥤ Scheme where
  obj U := Spec ↧(s2v_i1a_chartInvariants X G a U.1.1 U.2)
  map {U V} f := Spec.map
    (s2v_i1ahi_invariantRestriction X G a U.1.1 V.1.1 (leOfHom f) U.2 V.2)
  map_id U := by
    have he : s2v_i1ahi_invariantRestriction X G a U.1.1 U.1.1 le_rfl U.2 U.2 = 𝟙 _ := by
      ext r
      change (X.left.presheaf.map (𝟙 (Opposite.op U.1.1))).hom r.val = r.val
      rw [X.left.presheaf.map_id]
      rfl
    rw [he, Spec.map_id]
  map_comp {U V W} f g := by
    rw [← Spec.map_comp, s2v_i1ahi_invariantRestriction_comp]

example (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.affineOpens) (hi : ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1) :
    (s2v_i1ahi_chartDiagram X G a).obj ⟨U, hi⟩ =
      Spec ↧(s2v_i1a_chartInvariants X G a U.1 hi) := rfl

lemma s2v_i1ahi_chartDiagram_openImmersion
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    {U V : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}}
    (f : U ⟶ V) : IsOpenImmersion ((s2v_i1ahi_chartDiagram X G a).map f) :=
  s2v_i1ahi_transition_openImmersion X G a ha1 hamul U.1.1 V.1.1
    U.1.2 V.1.2 (leOfHom f) U.2 V.2

lemma s2v_i1ahi_chartDiagram_square
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    {U V : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}}
    (f : U ⟶ V) :
    s2v_i1a_affineQuotientMap X G a U.1.1 U.2 ≫
        (s2v_i1ahi_chartDiagram X G a).map f =
      X.left.homOfLE (leOfHom f) ≫ s2v_i1a_affineQuotientMap X G a V.1.1 V.2 :=
  s2v_i1ahi_transition_square X G a U.1.1 V.1.1 (leOfHom f) U.2 V.2

end HodgeLean.Foundations.Program

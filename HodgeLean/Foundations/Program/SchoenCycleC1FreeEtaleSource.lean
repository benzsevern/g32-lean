import HodgeLean.Foundations.Program.SchoenCycleC1FreeFormalPullback
import HodgeLean.Foundations.Program.SchoenCycleC1SectionEtaleOpen

/-! # Actual etale source neighbourhoods at free orbit points -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A free point of the retained smooth curve orbit projection has an affine
neighbourhood on which that actual projection is etale. -/
theorem s2e_c1_free_point_etale_source_neighbourhood
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1)
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hfree : ∀ g, Point.map (a g) x = x → g = 1) :
    ∃ V : X.left.Opens, x.underlying ∈ V ∧ V ≤ q.left ⁻¹ᵁ U ∧
      IsAffineOpen V ∧ Etale (V.ι ≫ q.left) := by
  letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hcx : IsClosed ({x.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨x.left, by simp⟩).2
  have hcy : IsClosed ({q.left x.underlying} : Set Y.left) := by
    simpa only [Set.image_singleton] using q.left.isClosedMap {x.underlying} hcx
  have hb := s2e_c1_free_point_formal_pullback_bijective
    X Y hdim G a ha1 hamul hinj q hsurj hinv horbit U hU x hx hfree
  have he := s2e_c1_section_isEtaleAt_of_formal_pullback X Y q U hU x hx hcx hcy hb
  exact s2e_c1_source_etale_open_of_section_isEtaleAt X.left Y.left q.left U hU
    x.underlying hx he

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.SncIntersectionStalks
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Ported.Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-! Smooth finite intersections of a labelled SNC family. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every finite intersection of SNC branches on a smooth complex scheme is smooth. -/
theorem g32l4_snc_intersection_smooth
    (B : Over (Spec ↧ℂ)) [Smooth B.hom]
    (E : Scheme.DivisorFamily B.left) (hE : E.IsSnc) (J : Finset E.ι) :
    Smooth (s2c_subscheme B (J.sup E.component)).hom := by
  let I := J.sup E.component
  have hreg : IsRegular I.subscheme := by
    constructor
    intro q
    have hx : I.subschemeι q ∈ I.support := by
      change I.subschemeι q ∈ (I.support : Set B.left)
      rw [← I.range_subschemeι]
      exact ⟨q, rfl⟩
    have h := g32l4_snc_intersection_stalk B E hE J (I.subschemeι q) hx
    letI : IsRegularLocalRing (B.left.presheaf.stalk (I.subschemeι q) ⧸
        I.stalkIdeal (I.subschemeι q)) := h.1
    exact IsRegularLocalRing.of_ringEquiv (I.stalkQuotientEquiv q)
  change Smooth (I.subschemeι ≫ B.hom)
  exact (Scheme.smooth_iff_isRegular (I.subschemeι ≫ B.hom)).mpr hreg

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.SncIntersectionSmooth
import HodgeLean.Foundations.Program.G32Native.ConormalFramesOfCodimension

/-! Recover the exact smooth-intersection and conormal-frame invariant from SNC. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An SNC family has smooth finite intersections with conormal rank equal to the number of labels. -/
theorem g32l4_snc_intersection_regularity
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (E : Scheme.DivisorFamily B.left) (hE : E.IsSnc) (J : Finset E.ι) :
    Smooth (s2c_subscheme B (J.sup E.component)).hom ∧
    ∀ x : (J.sup E.component).subscheme,
      ∃ U : (J.sup E.component).subscheme.Opens, x ∈ U ∧ Nonempty
        (Scheme.Modules.restrict (s2c_conormal (J.sup E.component).subschemeι) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) : U.toScheme.Modules)) := by
  letI : Smooth B.hom := SmoothOfRelativeDimension.smooth n B.hom
  let I := J.sup E.component
  letI : Smooth (s2c_subscheme B I).hom := g32l4_snc_intersection_smooth B E hE J
  refine ⟨inferInstance, ?_⟩
  apply g32l4_conormal_frames_of_stalk_codimension B n I J.card
  intro q
  have hx : I.subschemeι q ∈ I.support := by
    change I.subschemeι q ∈ (I.support : Set B.left)
    rw [← I.range_subschemeι]
    exact ⟨q, rfl⟩
  exact (g32l4_snc_intersection_stalk B E hE J (I.subschemeι q) hx).2

end HodgeLean.Foundations.Program

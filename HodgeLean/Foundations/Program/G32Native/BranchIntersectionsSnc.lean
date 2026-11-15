import HodgeLean.Foundations.Program.G32Native.BranchIntersectionParameters
import HodgeLean.Ported.Hironaka.Scheme.Snc.Defs

/-! Convert the labelled intersection invariant to the existing SNC interface. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The all-intersection smoothness and conormal-frame invariant implies SNC. -/
theorem g32l4_isSnc_of_branch_intersections
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (E : Scheme.DivisorFamily B.left)
    (hintersections : ∀ J : Finset E.ι,
      Smooth (s2c_subscheme B (J.sup E.component)).hom ∧
      ∀ x : (J.sup E.component).subscheme,
        ∃ U : (J.sup E.component).subscheme.Opens, x ∈ U ∧ Nonempty
          (Scheme.Modules.restrict (s2c_conormal (J.sup E.component).subschemeι) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
              U.toScheme.Modules))) : E.IsSnc := by
  constructor
  · intro i
    have hi := (hintersections {i}).1
    rw [Finset.sup_singleton] at hi
    letI : Smooth ((E.component i).subschemeι ≫ B.hom) := hi
    exact ⟨fun x => isRegularLocalRing_stalk ((E.component i).subschemeι ≫ B.hom) x⟩
  · intro x
    obtain ⟨m, z, c, hz, hI⟩ :=
      g32l4_branch_intersection_parameters B n E.component hintersections x
    exact ⟨m, z, hz, c, c.injective, hI⟩

end HodgeLean.Foundations.Program

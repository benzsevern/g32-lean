import HodgeLean.Foundations.Program.G32Native.ConormalFrameDimension
import HodgeLean.RealDefs.DegreeZero

/-! Positive conormal rank excludes the zero ideal on a smooth integral base. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A positive-rank conormal frame at every point prevents the ideal from being zero. -/
theorem g32l4_nonzero_of_positive_conormal_rank
    (B : Over (Spec ↧ℂ)) [Smooth B.hom] [IsIntegral B.left]
    (I : B.left.IdealSheafData) (m : ℕ) (hm : 0 < m)
    (hframe : ∀ x : (s2c_subscheme B I).left,
      ∃ U : (s2c_subscheme B I).left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict
          (s2c_conormal (s2c_subschemeι B I).left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin m) :
            U.toScheme.Modules))) : I ≠ ⊥ := by
  intro hI
  subst I
  let Q := s2c_subscheme B ⊥
  let j := s2c_subschemeι B ⊥
  letI : IsIso j.left :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr rfl
  letI : IsIntegral Q.left := IsIntegral.of_isIso (inv j.left)
  let n := TopologicalSpace.dim B.left
  letI : SmoothOfRelativeDimension n B.hom := inferInstance
  letI : SmoothOfRelativeDimension n Q.hom := by
    change SmoothOfRelativeDimension n (j.left ≫ B.hom)
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (j.left ≫ B.hom))
  letI : SmoothOfRelativeDimension (n + 0) B.hom := by
    simpa only [add_zero] using (inferInstance : SmoothOfRelativeDimension n B.hom)
  let x : Q.left := Classical.choice inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := hframe x
  have heq := g32l4_conormal_frame_rank_eq Q B n 0 j x U hx m e
  omega

end HodgeLean.Foundations.Program

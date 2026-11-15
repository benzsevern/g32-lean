import HodgeLean.Foundations.Program.G32Native.PELSplitReference
import HodgeLean.Foundations.Abdulali.RationalCentralizer

noncomputable section
open scoped Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Quaternion conjugation converts the reference pullback action into a
covariant algebra representation. -/
def pelReferenceQuaternionAction (R : PELSplitReference) :
    ℍ[ℚ, -3, 0, R.b] →ₐ[ℚ] Module.End ℚ (HQ R.B.X 1) where
  toFun q := (abelianEnd0Action R.B.X (R.end0 (star q))).unop
  map_one' := by simp
  map_zero' := by simp
  map_add' q r := by simp
  map_mul' q r := by simp
  commutes' q := by
    have hs : star (algebraMap ℚ ℍ[ℚ, -3, 0, R.b] q) =
        algebraMap ℚ ℍ[ℚ, -3, 0, R.b] q := by
      ext <;> simp [QuaternionAlgebra.algebraMap_eq]
    change (abelianEnd0Action R.B.X (R.end0 (star (algebraMap ℚ _ q)))).unop = _
    rw [hs, R.end0.commutes, (abelianEnd0Action R.B.X).commutes]
    rfl

/-- The covariant generator has the sign forced by quaternion conjugation. -/
theorem pelReferenceQuaternionAction_eisenstein (R : PELSplitReference) :
    pelReferenceQuaternionAction R ⟨0, 1, 0, 0⟩ = -R.B.W.J := by
  have hs : star (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, R.b]) = -⟨0, 1, 0, 0⟩ := by
    ext <;> simp
  rw [R.eisenstein]
  change (abelianEnd0Action R.B.X (R.end0 (star _))).unop = _
  rw [hs, map_neg, map_neg]
  rfl

/-- The reference Rosati equation passes to the covariant representation. -/
theorem pelReferenceQuaternionAction_rosati (R : PELSplitReference)
    (q : ℍ[ℚ, -3, 0, R.b]) (z w : HQ R.B.X 1) :
    polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate
      (pelReferenceQuaternionAction R q z) w =
    polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate
      z (pelReferenceQuaternionAction R (star q) w) := by
  change polarizationForm _ _ ((abelianEnd0Action R.B.X (R.end0 (star q))).unop z) w =
    polarizationForm _ _ z ((abelianEnd0Action R.B.X (R.end0 (star (star q)))).unop w)
  simpa only [star_star] using R.adjoint (star q) z w

#print axioms pelReferenceQuaternionAction
#print axioms pelReferenceQuaternionAction_eisenstein
#print axioms pelReferenceQuaternionAction_rosati
end HodgeLean.Foundations.Program.GeneralTypeIII

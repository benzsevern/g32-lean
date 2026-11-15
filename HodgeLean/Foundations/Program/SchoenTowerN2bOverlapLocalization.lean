import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual principal open chart has its section algebra localized through its inclusion map. -/
theorem n2b_sections_isLocalization_of_principal_range
    {U V : Scheme.{0}} [IsAffine U] (j : V ⟶ U) [IsOpenImmersion j]
    (s : Γ(U, ⊤)) (hj : j.opensRange = U.basicOpen s) :
    letI := j.appTop.hom.toAlgebra
    IsLocalization.Away s Γ(V, ⊤) := by
  letI := j.appTop.hom.toAlgebra
  have hr : Set.range j = Set.range (U.basicOpen s).ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg SetLike.coe hj
  let e := IsOpenImmersion.isoOfRangeEq j (U.basicOpen s).ι hr
  have he : e.hom ≫ (U.basicOpen s).ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac j (U.basicOpen s).ι hr
  let φ : Γ((U.basicOpen s).toScheme, ⊤) ≃ₐ[Γ(U, ⊤)] Γ(V, ⊤) :=
    { (asIso e.hom.appTop).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        change e.hom.appTop.hom ((U.basicOpen s).ι.appTop.hom r) = j.appTop.hom r
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he] }
  exact IsLocalization.isLocalization_of_algEquiv (.powers s) φ

end HodgeLean.Foundations.Program

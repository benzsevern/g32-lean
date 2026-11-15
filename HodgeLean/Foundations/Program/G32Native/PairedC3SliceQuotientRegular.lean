import HodgeLean.Foundations.Program.G32Native.PairedC3AffineSliceCoefficient

/-! # Cancellation on the original affine slice quotient -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A branch equation remains regular modulo the actual slice ideal. The
injection from the quotient by the kernel into slice sections transports
cancellation, without a choice of an affine presentation of the slice. -/
theorem pairedC3_slice_quotient_branch_regular
    {Q X : Scheme} [IsIntegral Q] (i : Q ⟶ X) [IsClosedImmersion i]
    (D : X.IdealSheafData) (hproper : (D.comap i).support ≠ ⊤)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (u : Γ(X, U)) (hu : D.ideal U = Ideal.span {u}) :
    IsRegular (Ideal.Quotient.mk (i.ker.ideal U) u) := by
  have hreg := paired_c3_restricted_branch_regular i D hproper U u hu
  rw [Scheme.Hom.ker_apply]
  apply (Commute.isRegular_iff (fun _ => mul_comm _ _)).mpr
  intro a b hab
  apply (i.app U.1).hom.kerLift_injective
  apply hreg
  change (i.app U.1).hom u * (i.app U.1).hom.kerLift a =
    (i.app U.1).hom u * (i.app U.1).hom.kerLift b
  simpa only [map_mul, RingHom.kerLift_mk] using
    congrArg (i.app U.1).hom.kerLift hab

#print axioms pairedC3_slice_quotient_branch_regular
end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedResidualIntersection
import HodgeLean.Foundations.Program.SchoenCycleS3AffineQuotientChart

/-! # The ideal required by a specified residual hyperplane -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Identification over the slice with a specified subscheme is equivalent to equality of its ideal. -/
theorem residual_intersection_subscheme_iff
    {S : Scheme} {P V : Over S} (i : P ⟶ V) [IsClosedImmersion i.left]
    (J : V.left.IdealSheafData) (K : P.left.IdealSheafData) :
    (∃ e : (residualIntersection i J).left ≅ K.subscheme,
      e.hom ≫ K.subschemeι = (residualIntersectionFirst i J).left) ↔
      J.comap i.left = K := by
  constructor
  · rintro ⟨e, he⟩
    have hk := congrArg Scheme.Hom.ker he
    rw [Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι,
      residualIntersectionFirst_kernel] at hk
    exact hk.symm
  · intro hk
    exact s2e_closedImmersion_subschemeIso (residualIntersectionFirst i J).left K
      ((residualIntersectionFirst_kernel i J).trans hk)

#print axioms residual_intersection_subscheme_iff
end HodgeLean.Foundations.Program.G32Native

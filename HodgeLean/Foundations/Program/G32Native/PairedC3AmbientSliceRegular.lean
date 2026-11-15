import HodgeLean.Foundations.Program.G32Native.PairedC3SliceQuotientRegular

/-! # Ambient regularity near the integral slice -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A branch equation with proper restriction to a nonempty integral slice
is nonzero, hence regular in the integral ambient affine ring. -/
theorem pairedC3_ambient_branch_regular_near_slice
    {Q X : Scheme} [IsIntegral Q] [IsIntegral X]
    (i : Q ⟶ X) [IsClosedImmersion i]
    (D : X.IdealSheafData) (hproper : (D.comap i).support ≠ ⊤)
    (U : X.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (u : Γ(X, U)) (hu : D.ideal U = Ideal.span {u}) : IsRegular u := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (i ⁻¹ᵁ U.1))
  letI : Nonempty U.1 := ⟨⟨i x.val, x.property⟩⟩
  have hreg := paired_c3_restricted_branch_regular i D hproper U u hu
  have hleft : IsLeftRegular ((i.app U.1).hom u) := hreg
  have hboth : IsRegular ((i.app U.1).hom u) :=
    (Commute.isRegular_iff (fun _ => mul_comm _ _)).mpr hleft
  apply IsRegular.of_ne_zero
  intro hz
  apply hboth.ne_zero
  rw [hz, map_zero]

#print axioms pairedC3_ambient_branch_regular_near_slice
end HodgeLean.Foundations.Program.G32Native

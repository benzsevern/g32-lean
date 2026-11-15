import HodgeLean.RealDefs.Compare.MarkmanDiscriminant

noncomputable section
open Module
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open HodgeLean.RealDefs.Compare.Markman

namespace HodgeLean.Foundations.Program.G32Native

/-- The homological and cohomological determinant classes agree in even quadratic dimension.
Source: van Geemen, LNM 1594, §5.4; contraction and the negative-action comparison in
`MarkmanTransport.homologyEquiv_gram` and `MarkmanDiscriminant.weilDetClass_negative_of_even`.
The transpose action on homology intertwines with the negative action after contraction. -/
theorem polarization_dual_determinant
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {a : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (J : {J : Module.End ℚ V // J ∘ₗ J = a • LinearMap.id})
    {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) (hR : IsRosatiSkew ω J.1)
    (hE : (riemannForm ω).IsAlt) (hn : (riemannForm ω).Nondegenerate)
    (heven : Even (finrank (QuadraticAlgebra ℚ a 0) (WithJ V J))) :
    weilDetClass (riemannForm ω) (transposeAction J) (riemannForm_skew J hR) hE hn =
      weilDetClass (dualForm hω) J ((isRosatiSkew_iff_dualForm hω J.1).1 hR)
        (isAlt_dualForm hω) (nondegenerate_dualForm hω) := by
  rw [← weilDetClass_negative_of_even (dualForm hω) J
    ((isRosatiSkew_iff_dualForm hω J.1).1 hR)
    (isAlt_dualForm hω) (nondegenerate_dualForm hω) heven]
  let b := Module.finBasis (QuadraticAlgebra ℚ a 0)
    (WithJ (Dual ℚ V) (transposeAction J))
  unfold weilDetClass
  rw [detClass_eq _ _ b, detClass_eq _ _ (b.map (homologyEquiv J hω hR))]
  congr 1
  apply Units.ext
  change gramDetℚ _ b = gramDetℚ _ (b.map (homologyEquiv J hω hR))
  have hg := homologyEquiv_gram J hω hR b
  have hd := congrArg Matrix.det hg
  have hc := congrArg (fun z : QuadraticAlgebra ℚ a 0 => z.re) hd
  exact hc.symm

#print axioms polarization_dual_determinant
end HodgeLean.Foundations.Program.G32Native

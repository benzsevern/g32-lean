import HodgeLean.Foundations.Program.SchoenTransferJ12AbelianSection
import HodgeLean.Foundations.Program.SchoenTransferJ12AbelComparison

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
namespace HodgeLean.Foundations.Program

/-- Retain the actual Abel map, its H1 identification and the multiplication section of the generating factor. -/
theorem s4_selected_curve_abel_factor_data
    (Y A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ A) (hf : Function.Injective (homPullback f 1)) :
    ∃ (B : Over (Spec ↧ℂ)) (hGroup : GrpObj B),
      letI := hGroup
      ∃ hComm : IsCommMonObj B,
      letI := hComm
      ∃ hInt : IsIntegral B.left,
      letI := hInt
      ∃ hSmooth : Smooth B.hom,
      letI := hSmooth
      ∃ hProjective : IsProjective B.hom,
      letI := hProjective
      ∃ (j : Y ⟶ B) (π : B ⟶ A) (s : A ⟶ B) (N : ℕ)
        (hj : Function.Bijective (homPullback j 1)),
        IsMonHom π ∧ IsMonHom s ∧ 0 < N ∧
        (homPullback j 1).comp (homPullback π 1) = homPullback f 1 ∧
        s ≫ π = (N : AbelianEnd A).hom := by
  letI := connectedSpace_complexPoint Y
  let p : ComplexPoint Y := Classical.choice inferInstance
  have h : Module.finrank ℂ (Fin (TopologicalSpace.dim Y.left) → ℂ) = 1 := by
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one] using hdim
  obtain ⟨j, hj, hbij⟩ := s4_selected_algebraic_abel_exists Y hdim p
  let B := model (C := ComplexPoint Y) h
  letI : IsCommMonObj B := isCommMonObj_of_complexSelfProductIntegral B
    (complexSelfProductIntegral_of_isIntegral B)
  obtain ⟨π, hπ, N, s, hs, hN, hfac, hsec⟩ :=
    s4_selected_abel_factor_section Y A h p j hj f hf
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    j, π, s, N, hbij, hπ, hs, hN, hfac, hsec⟩

#print axioms s4_selected_curve_abel_factor_data
end HodgeLean.Foundations.Program

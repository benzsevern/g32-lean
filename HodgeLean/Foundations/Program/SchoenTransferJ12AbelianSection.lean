import HodgeLean.Foundations.Program.SchoenTransferJ12AbelFactorH1
import HodgeLean.Foundations.AbelianQuotient.Basic
import HodgeLean.Foundations.AbelianQuotient.SurjectiveSection

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

/-- A generating curve's actual Abel factor has a positive multiplication section.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§5.3 and 11.4. -/
theorem s4_selected_abel_factor_section
    (X A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [ConnectedSpace (ComplexPoint X)]
    (h : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1)
    (p : ComplexPoint X) (j : X ⟶ model h)
    (hj : ∀ x, Point.map j x = modelAbel h p x)
    (f : X ⟶ A) (hf : Function.Injective (homPullback f 1)) :
    ∃ (π : model h ⟶ A) (_ : IsMonHom π) (N : ℕ) (s : A ⟶ model h),
      IsMonHom s ∧ 0 < N ∧
      (homPullback j 1).comp (homPullback π 1) = homPullback f 1 ∧
      s ≫ π = (N : AbelianEnd A).hom := by
  let D := model (C := ComplexPoint X) h
  letI : IsCommMonObj D := isCommMonObj_of_complexSelfProductIntegral D
    (complexSelfProductIntegral_of_isIntegral D)
  obtain ⟨π, hπ, heq⟩ := s4_selected_abel_factor_H1 X A h p j hj f
  letI := hπ
  have hi : Function.Injective (homPullback π 1) := by
    intro v w hvw
    apply hf
    rw [← LinearMap.congr_fun heq v, ← LinearMap.congr_fun heq w]
    exact congrArg (homPullback j 1) hvw
  let DA : AbelianQuotient.Variety := ⟨D, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
  let AA : AbelianQuotient.Variety := ⟨A, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
  let πA : AbelianQuotient.Hom DA AA := ⟨π, hπ⟩
  have hs := AbelianQuotient.surjective_of_injective_h1 πA hi
  obtain ⟨N, s, hN, hsec⟩ := AbelianQuotient.exists_multiplication_section πA hs
  exact ⟨π, hπ, N, s.hom, s.mon, hN, heq, hsec⟩

#print axioms s4_selected_abel_factor_section

end HodgeLean.Foundations.Program

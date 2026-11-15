import HodgeLean.Foundations.Program.SchoenTransferJ12AnalyticFactor
import HodgeLean.Foundations.Program.SchoenTransferJ12GroupReflection
import HodgeLean.Foundations.AnalyticAlbanese.Realization.Algebraization

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Manifold
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local irreducible] Point.map

/-- The pointed factor through the actual Abel model is algebraic and respects its group law. -/
theorem s4_selected_algebraic_abel_factor
    (X A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [ConnectedSpace (ComplexPoint X)]
    (h : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1)
    (p : ComplexPoint X) (j : X ⟶ model h)
    (hj : ∀ x, Point.map j x = modelAbel h p x)
    (f : X ⟶ A) (hp : Point.map f p = 1) :
    ∃ π : model h ⟶ A, IsMonHom π ∧ j ≫ π = f := by
  let E := Fin (TopologicalSpace.dim X.left) → ℂ
  let C := ComplexPoint X
  let Λ := b3_periodLattice E C
  let F := b3_periodF E C
  let hF := b3_isWeightOne (C := C) h
  let Q := polarization (C := C) h
  have hQ : b2_IsRiemannForm Λ F Q :=
    b3_intersectionForm_isRiemannForm h Q (b3_exists_intersectionForm h).choose_spec
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete F hF
  let M := model (C := C) h
  letI : IsCommMonObj M := isCommMonObj_of_complexSelfProductIntegral M
    (complexSelfProductIntegral_of_isIntegral M)
  let θ := theta (C := C) h
  obtain ⟨H, hH, hfactor⟩ := s4_selected_analytic_abel_factor X A h p f hp
  have hθinv : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim M.left) → ℂ)
      𝓘(ℂ, b5_V Λ F) ω θ.symm :=
    (b5_theta_holomorphicFunctions Λ F hF Q hQ).2.1
  let K : ComplexPoint M → ComplexPoint A := fun z => Additive.toMul (H (θ.symm z))
  obtain ⟨π, hπ⟩ := gagam_algebraize M A K (hH.comp hθinv)
  have he (z) : Point.map π (θ z) = Additive.toMul (H z) := by
    exact (congrFun hπ (θ z)).trans
      (congrArg (fun t => Additive.toMul (H t)) (θ.symm_apply_apply z))
  have hθ0 : θ 0 = (1 : ComplexPoint M) := (thetaNormalization (C := C) h).1
  have hθadd (z w) : θ (z + w) = θ z * θ w :=
    (thetaNormalization (C := C) h).2.1 z w
  have hmon : IsMonHom π :=
    s4_selected_group_reflection _ M A θ.toEquiv hθ0 hθadd H π he
  refine ⟨π, hmon, ?_⟩
  apply b55_hom_ext
  funext x
  have hx := (congrArg (Point.map π) (hj x)).trans
    ((he (analyticAbel h p x)).trans (congrArg Additive.toMul (hfactor x)))
  simpa only [Point.map_comp_apply, toMul_ofMul] using hx

#print axioms s4_selected_algebraic_abel_factor

end HodgeLean.Foundations.Program

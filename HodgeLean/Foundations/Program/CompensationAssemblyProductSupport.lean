import HodgeLean.Foundations.Program.CompensationAssemblyPrimeSupport
import HodgeLean.Foundations.Program.CompensationAssemblySurfaceTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_cohomologyHomeomorphEquiv_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) (c : Cohomology ℚ (TopCat.of X) n) :
    cohomologyHomeomorphEquiv e n c =
      cohomologyMap ℚ n (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) c := by
  apply (cohomologyHomeomorphEquiv e n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change c = (cohomologyMap ℚ n (TopCat.ofHom ⟨e, e.continuous⟩))
    (cohomologyMap ℚ n (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) c)
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  have h : (TopCat.ofHom ⟨e, e.continuous⟩) ≫
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) = 𝟙 (TopCat.of X) := by
    apply ConcreteCategory.hom_ext
    exact e.symm_apply_apply
  rw [h, cohomologyMap_id]
  rfl

theorem cq_projection_component_restriction_zero
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (x : (A ⊗ Y).left) {p : ℕ} (hx : Order.coheight x = p) :
    cohomologyMap ℚ (2 * p)
      (cq_fibreProductMap
        (TopologicalSpace.Opens.inclusion' (X := TopCat.of (ComplexPoint A))
          (cycleComponentAnalyticClosedSupport A
            ((CategoryTheory.CartesianMonoidalCategory.fst A Y).left x)).compl)
        (TopCat.of (ComplexPoint Y)))
      (cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
        (2 * p) (cupComparison (A ⊗ Y) (2 * p)
          (cycleComponentSheafClass (A ⊗ Y) x hx))) = 0 := by
  let S := cycleComponentAnalyticClosedSupport A
    ((CategoryTheory.CartesianMonoidalCategory.fst A Y).left x)
  let U := S.compl
  let h := HodgeLean.Foundations.complexPointProdHomeomorph A Y
  let i := TopologicalSpace.Opens.inclusion' (X := TopCat.of (ComplexPoint A)) U
  let g := cq_fibreProductMap i (TopCat.of (ComplexPoint Y))
  let f := g ≫ TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  rw [cq_cohomologyHomeomorphEquiv_apply, ← LinearMap.comp_apply,
    ← cohomologyMap_comp]
  apply cq_component_class_pullback_zero (A ⊗ Y) x hx _ f
  rintro ⟨a, b⟩ hz
  have hz' := cq_component_support_map
    (CategoryTheory.CartesianMonoidalCategory.fst A Y) x (f (a, b)) hz
  have heq : Point.map (CategoryTheory.CartesianMonoidalCategory.fst A Y)
      (f (a, b)) = a.1 := by
    exact congrArg Prod.fst (h.apply_symm_apply (a.1, b))
  rw [heq] at hz'
  exact a.2 hz'

theorem cq_projection_prime_trace_zero
    (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight
      ((CategoryTheory.CartesianMonoidalCategory.fst A Y).left x) ≠ 3) :
    cq_surfaceModelTrace (TopCat.of (ComplexPoint A)) Y hY 6
      (cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
        10 (cupComparison (A ⊗ Y) 10
          (cycleComponentSheafClass (A ⊗ Y) x hx))) = 0 := by
  apply cq_projection_image_singular_restriction_injective A Y hA hY x hx himage
  rw [← cq_surfaceModelTrace_naturality,
    cq_projection_component_restriction_zero A Y x hx, map_zero, map_zero]

end HodgeLean.Foundations.Program

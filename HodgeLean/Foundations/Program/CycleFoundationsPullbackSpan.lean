import HodgeLean.Foundations.Program.CycleFoundationsZeroSectionProjection

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program

variable (A B : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]

theorem cfd_zero_section_span (p : ℕ) (x : HQ (B ⊗ A) (2 * p))
    (hx : x ∈ cfd_cycleSpan (B ⊗ A) p) :
    homPullback (lift (𝟙 B) (1 : B ⟶ A)) (2 * p) x ∈ cfd_cycleSpan B p := by
  let d := TopologicalSpace.dim A.left
  obtain ⟨I, _⟩ := cfd_top_integration A d rfl
  obtain ⟨t, ht, hIt⟩ := cfd_top_class A d rfl I
  rw [cfd_zero_section_projection A B d rfl I t hIt]
  letI : Smooth (snd B A).left := by
    change Smooth (Limits.pullback.snd B.hom A.hom)
    infer_instance
  have hpb : homPullback (snd B A) (2 * d) t ∈ cfd_cycleSpan (B ⊗ A) d :=
    cq_smooth_pullback_span_core (snd B A) d (Submodule.mem_map_of_mem ht)
  have hc : (cupProductOf (B ⊗ A)).cup
      (show 2 * p + 2 * d = 2 * (p + d) by omega)
      x (homPullback (snd B A) (2 * d) t) ∈ cfd_cycleSpan (B ⊗ A) (p + d) :=
    (hc9k_cycleClassMultiplicative (B ⊗ A)).mem _ _ _ hx hpb
  have hp := cfd_projection_span_map_le B A d (p + d) p rfl I
    (show 2 * (p + d) = 2 * p + 2 * d by omega) (Submodule.mem_map_of_mem hc)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, CupProduct.castEquiv_cup] using hp

theorem cfd_morphism_pullback_span (f : B ⟶ A) (p : ℕ)
    (x : HQ A (2 * p)) (hx : x ∈ cfd_cycleSpan A p) :
    homPullback f (2 * p) x ∈ cfd_cycleSpan B p := by
  let g := (cfd_shear f).hom ≫ snd B A
  letI : Smooth g.left := cfd_shear_smooth f
  have hg : homPullback g (2 * p) x ∈ cfd_cycleSpan (B ⊗ A) p :=
    cq_smooth_pullback_span_core g p (Submodule.mem_map_of_mem hx)
  have hs := cfd_zero_section_span A B p _ hg
  have hcomp : lift (𝟙 B) (1 : B ⟶ A) ≫ g = f := by
    simp [g, cfd_shear, MonObj.comp_mul]
  rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hcomp] at hs
  exact hs

end HodgeLean.Foundations.Program

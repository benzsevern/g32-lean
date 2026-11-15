import HodgeLean.Foundations.Program.SchoenSelectedGeometryCurveModels
import HodgeLean.Foundations.Program.G32SelectedRealizationMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem s0_curve_model_action
    {G C : Type} [Group G] [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction G C] [FaithfulSMul G C]
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (e : C ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω e)
    (hi : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    ∃ a : G → (X ⟶ X),
      (∀ g x, Point.map (a g) (e x) = e (g • x)) ∧
      a 1 = 𝟙 X ∧ (∀ u v, a (u * v) = a v ≫ a u) ∧ Function.Injective a := by
  classical
  choose a ha using fun g ↦ s0_curve_model_map X X e e hi he _ (hG g)
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · apply g32x_over_hom_ext X
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change Point.map (a 1) (e y) = e y
    simpa only [one_smul] using ha 1 y
  · intro u v
    apply g32x_over_hom_ext X
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change Point.map (a (u * v)) (e y) = Point.map (a u) (Point.map (a v) (e y))
    rw [ha, ha, ha, mul_smul]
  · intro u v huv
    exact eq_of_smul_eq_smul (fun x : C ↦ e.injective (by rw [← ha, ← ha, huv]))

#print axioms s0_curve_model_action

theorem s0_curve_model_action_invariant
    {G C D : Type} [Group G] [MulAction G C]
    [TopologicalSpace C] [TopologicalSpace D]
    (X Y : Over (Spec ↧ℂ)) [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [IsProjective Y.hom]
    (e : C ≃ₜ ComplexPoint X) (d : D → ComplexPoint Y)
    (a : G → (X ⟶ X)) (p : X ⟶ Y) (F : C → D)
    (ha : ∀ g x, Point.map (a g) (e x) = e (g • x))
    (hp : ∀ x, Point.map p (e x) = d (F x))
    (hF : ∀ (g : G) (x : C), F (g • x) = F x) :
    ∀ g, a g ≫ p = p := by
  intro g
  apply g32x_over_hom_ext Y
  funext z
  obtain ⟨x, rfl⟩ := e.surjective z
  change Point.map p (Point.map (a g) (e x)) = Point.map p (e x)
  rw [ha, hp, hp, hF]

#print axioms s0_curve_model_action_invariant

end HodgeLean.Foundations.Program

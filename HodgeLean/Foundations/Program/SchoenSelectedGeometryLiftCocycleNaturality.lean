import HodgeLean.Foundations.Program.CurveJacobianRest2Integ
import HodgeLean.Foundations.Singular.Cup

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Integration defined by lifting simplices commutes with precomposition. -/
theorem s0_lift_integral_comp
    {V J X Y : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup J] [TopologicalSpace J] [TopologicalSpace X] [TopologicalSpace Y]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    (f : Y → J) (hf : Continuous f) (g : X → Y) (hg : Continuous g) (ℓ : V →+ ℂ)
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) :
    b3Rest2_LI π hπ (f ∘ g) (hf.comp hg) ℓ σ =
      b3Rest2_LI π hπ f hf ℓ
        ((TopCat.toSSet.map (TopCat.ofHom ⟨g, hg⟩)).app _ σ) := by
  let τ := (⟨g, hg⟩ : C(X, Y)).comp ((TopCat.of X).toSSetObjEquiv _ σ)
  obtain ⟨F, hF⟩ := b3Rest2_exists_lift π hπ f hf τ
  exact (b3Rest2_LI_eq π hπ (f ∘ g) (hf.comp hg) ℓ σ F hF).trans
    (b3Rest2_LI_eq π hπ f hf ℓ
      ((TopCat.toSSet.map (TopCat.ofHom ⟨g, hg⟩)).app _ σ) F hF).symm

#print axioms s0_lift_integral_comp
/-- Pullback of a lifted integration class is the integration class of the composite. -/
theorem s0_lift_cohomology_comp
    {V J X Y : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup J] [TopologicalSpace J] [TopologicalSpace X] [TopologicalSpace Y]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    (f : Y → J) (hf : Continuous f) (g : X → Y) (hg : Continuous g) (ℓ : V →+ ℂ) :
    AlgebraicTopology.Singular.cohomologyMap ℂ 1 (TopCat.ofHom ⟨g, hg⟩)
        (HodgeLean.Foundations.Singular.cohomologyClass (TopCat.of Y) 1
          (b3Rest2_liftCocycle π hπ f hf ℓ)) =
      HodgeLean.Foundations.Singular.cohomologyClass (TopCat.of X) 1
        (b3Rest2_liftCocycle π hπ (f ∘ g) (hf.comp hg) ℓ) := by
  apply HodgeLean.Foundations.Singular.cohomologyMap_class
  apply cochain_ext_simplex_b3Rest2
  intro σ
  rw [AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map,
    b3Rest2_liftCocycle_apply, b3Rest2_liftCocycle_apply]
  exact s0_lift_integral_comp π hπ f hf g hg ℓ σ

#print axioms s0_lift_cohomology_comp
end HodgeLean.Foundations.Program

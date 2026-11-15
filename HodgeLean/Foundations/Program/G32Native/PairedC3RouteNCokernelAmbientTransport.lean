import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComparisonCokernelFactor
import HodgeLean.Foundations.AlgebraicGeometry.ConormalIsoComparison

/-! # Cokernel transport retaining the ambient comparison map -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Equality of the ambient maps identifies the natural conormal cokernels,
independently of the chosen factorization between the immersed schemes.
The induced map of target conormals is the identity.
Source: Hartshorne, Algebraic Geometry, II.8, naturality of conormal pullback. -/
def pairedConormalCokernelIsoOfAmbient
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f f' : W' ⟶ W) (hf : f = f') (g g' : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (h' : g' ≫ i = i' ≫ f') :
    cokernel (comparisonMap i i' f g h) ≅ cokernel (comparisonMap i i' f' g' h') := by
  subst f'
  let e₀ := unionConormalComparisonPrefixIso i i' f g h
  let e₁ := unionConormalComparisonPrefixIso i i' f g' h'
  let e := e₀ ≪≫ e₁.symm
  apply cokernel.mapIso _ _ e (Iso.refl _)
  simp only [Iso.refl_hom, Category.comp_id]
  rw [unionConormal_comparisonMap_eq_prefix, unionConormal_comparisonMap_eq_prefix]
  change e₀.hom ≫ (Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h) =
    (e₀.hom ≫ e₁.inv) ≫ (e₁.hom ≫
      (Scheme.Modules.pullback i').map (idealPullbackMap i i' f g' h'))
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [idealPullbackMap_eq_of_ambient i i' f g g' h h']

#print axioms pairedConormalCokernelIsoOfAmbient
end HodgeLean.Foundations.Program.G32Native

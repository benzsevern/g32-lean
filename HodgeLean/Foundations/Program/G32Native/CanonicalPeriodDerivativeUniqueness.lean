import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs
import HodgeLean.Foundations.Program.G32Native.DiscreteQuotientLiftDerivatives

/-! # Original derivatives of local lifts of the retained canonical period quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open Filter Topology
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Two differentiable local lifts through the original canonical period
quotient retain the same original derivative in the retained form coordinates. -/
theorem canonicalPeriodQuotient_fderiv_eq (G : CanonicalAbelGeometry)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {f g : X → Fin (G.k + 1) → ℂ} {x : X}
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (hq : (fun z => canonicalPeriodQuotient G (f z)) =ᶠ[𝓝 x]
      (fun z => canonicalPeriodQuotient G (g z))) : fderiv ℂ f x = fderiv ℂ g x := by
  let h := Module.finrank_fin_fun (n := 1) ℂ
  let Λ := b3_periodLattice (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z)
  let F := b3_periodF (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z)
  letI := b3_periodLattice_finite (C := AlgebraicGeometry.ComplexPoint G.Z) h
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := AlgebraicGeometry.ComplexPoint G.Z) h)
  let L := (quotientBasisEquiv h (canonicalFormBasis G)).symm
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L.toLinearMap
  exact fderiv_eq_of_discrete_quotient_lifts L.toAddEquiv.toAddMonoidHom hL L.injective
    (b2_latticeMap Λ F).range hf hg hq

#print axioms canonicalPeriodQuotient_fderiv_eq
end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientForms
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelLocalPrimitives
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.DiscCoefficientComparison

/-! # Local Abel primitives in the original normalized curve coordinate -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Manifold Filter Set
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Local form coefficients retain the original basis expansion. -/
theorem discCoefficient_basis_pairing
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (b3_HolForm E C))
    (a : ι → ℂ) (q : C) (u : E) (z : ℂ) :
    b3A_discCoef (b.equivFun.symm a).val q u z = ∑ i, a i * b3A_discCoef (b i).val q u z := by
  let ev : b3_HolForm E C →ₗ[ℂ] ℂ := {
    toFun := fun θ => b3A_discCoef θ.val q u z
    map_add' := fun θ η => b3A_discCoef_add θ η q u z
    map_smul' := fun c θ => b3A_discCoef_smul c θ q u z }
  change ev (b.equivFun.symm a) = ∑ i, a i * ev (b i)
  rw [b.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul]

#print axioms discCoefficient_basis_pairing
end HodgeLean.Foundations.Program.G32Native

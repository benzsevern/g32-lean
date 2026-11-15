import HodgeLean.Foundations.Program.G32Native.JointSelectedPrefixProducer
import HodgeLean.Foundations.Program.G32Native.SelectedCoverSpec

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Papers HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
namespace ResidueSelected

attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Instantiate the shared joint producer at the migrated cover choice. -/
theorem jointSelectedPrefix_spec {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    let X := Classical.choose (g32y_cover_spec D t hg B)
    ∀ (S : g32p_Supplier) (hS : g32p_Admissible X.aut S),
      ∃ R : G32JointPrefix X.J X.aut S, R.P = X.part S hS := by
  intro X S hS
  obtain ⟨hJ, hGrp, hAut⟩ := Classical.choose_spec (g32y_cover_spec D t hg B)
  exact jointSelectedPrefix_exists D t hg
    (Classical.choose (g32x_deck_realization D t))
    (Classical.choose_spec (g32x_deck_realization D t)) X hJ hAut hGrp S hS

#print axioms jointSelectedPrefix_spec
end ResidueSelected
end HodgeLean.Foundations.Program

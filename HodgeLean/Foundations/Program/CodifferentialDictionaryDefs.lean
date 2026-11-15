import HodgeLean.Foundations.Program.CoverDictionaryDefs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs

/-! Direction labels for the cover dictionary. HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- The r-column representation is labelled zero and its conjugate one.
Source: G32 v0.16, §5.5(6); CodifferentialComparison.md, 6e-dictionary, item 2. -/
def b66d_dir {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
    {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
    (conj : Bool) : Fin 2 := if conj = S.conj then 0 else 1

example {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
    {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
    (conj : Bool) : b66d_dir S conj = (if conj = S.conj then 0 else 1) := rfl

end HodgeLean.Foundations.Program

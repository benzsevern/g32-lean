import HodgeLean.Foundations.BundleThom.InverseFrameContinuityHelpers

/-! # The fixed normal fibre topology is induced from the fixed total topology

A supplied actual local conormal frame identifies both topologies with its complex coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {Z : Scheme} (j : Q.left ⟶ Z) (k : ℕ)
private local instance (x : ComplexPoint Q) : TopologicalSpace (i1_normalFibre j x) :=
  i1_normalFibreTopology j x
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Inclusion of an actual normal fibre is an embedding for the specified dual and total topologies.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, local normal bundle charts. -/
theorem i1_normalFibreInclusion_isEmbedding_of_frame (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    Topology.IsEmbedding (fun v : i1_normalFibre j x =>
      (⟨x, v⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j))) := by
  let H := i1_normalFrameHomeomorph j k U E
  let h := i1_normalBasisHomeomorph j x k (i1_conormalFrameBasis j k U E x hx)
  let i : i1_normalFibre j x → {z : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
      z.proj ∈ Point.overOpen U} := fun v => ⟨⟨x, v⟩, hx⟩
  let f : i1_normalFibre j x → ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) :=
    fun v => (⟨x, hx⟩, h v)
  let g : ↥(Point.overOpen U : Set (ComplexPoint Q)) × (Fin k → ℂ) → i1_normalFibre j x :=
    fun p => h.symm p.2
  have hLI : Function.LeftInverse g f := fun v => h.symm_apply_apply v
  have hF : Topology.IsEmbedding f := hLI.isEmbedding
    (h.symm.continuous.comp continuous_snd) (continuous_const.prodMk h.continuous)
  have hI : Topology.IsEmbedding i := H.isEmbedding.of_comp_iff.mp hF
  exact Topology.IsEmbedding.subtypeVal.comp hI

end HodgeLean.Foundations.BundleThom

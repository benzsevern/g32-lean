import HodgeLean.Foundations.BundleThom.NormalFrameTrivializationHelpers
import HodgeLean.Foundations.BundleThom.NormalFibreEmbeddingHelpers
import HodgeLean.Foundations.BundleThom.LinearChartTransitionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! # Assembly of the actual analytic normal atlas

Local algebraic conormal frames give charts for the fixed fibre and total topologies.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
private local instance (x : ComplexPoint Q) : TopologicalSpace (i1_normalFibre j x) :=
  i1_normalFibreTopology j x
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Select an actual conormal frame around each supplied point of the smooth immersion.
Source: Hartshorne, Algebraic Geometry, II.8, local frames of the conormal of a smooth immersion. -/
def i1_smoothConormalFrameAt
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV] (x : ComplexPoint Q) :
    Σ U : Q.left.Opens,
      {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
        SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) // x ∈ Point.overOpen U} := by
  classical
  let ι : Q ⟶ Over.mk sV := Over.homMk j hj
  letI : IsClosedImmersion ι.left := ‹IsClosedImmersion j›
  letI : SmoothOfRelativeDimension (k + k) (Over.mk sV).hom :=
    ‹SmoothOfRelativeDimension (k + k) sV›
  apply Classical.choice
  obtain ⟨U, hx, ⟨E⟩⟩ :=
    HodgeLean.Foundations.Program.s2e_smooth_closedImmersion_conormal_frames
      Q (Over.mk sV) k k ι x.underlying
  exact ⟨⟨U, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫ E, hx⟩⟩⟩

/-- Assemble actual linear normal-frame charts into a fibre bundle for the fixed topologies.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, bundle atlases. -/
def i1_normalFiberBundle
    (frames : ∀ x : ComplexPoint Q, Σ U : Q.left.Opens,
      {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
        SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) // x ∈ Point.overOpen U}) :
    FiberBundle (Fin k → ℂ) (i1_normalFibre j) where
  totalSpaceMk_isInducing' b :=
    (i1_normalFibreInclusion_isEmbedding_of_frame j k (frames b).1 (frames b).2.1 b
      (frames b).2.2).isInducing
  trivializationAtlas' := {e | e.IsLinear ℂ}
  trivializationAt' b := i1_normalFrameTrivialization j k (frames b).1 (frames b).2.1
  mem_baseSet_trivializationAt' b := (frames b).2.2
  trivialization_mem_atlas' b :=
    i1_normalFrameTrivialization_isLinear j k (frames b).1 (frames b).2.1

/-- The linear normal atlas has continuous complex operator transitions.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex vector bundle atlases. -/
theorem i1_normalVectorBundle
    (frames : ∀ x : ComplexPoint Q, Σ U : Q.left.Opens,
      {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
        SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) // x ∈ Point.overOpen U}) :
    letI := i1_normalFiberBundle j k frames
    VectorBundle ℂ (Fin k → ℂ) (i1_normalFibre j) := by
  letI := i1_normalFiberBundle j k frames
  have hlinear (e : Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) (i1_normalFibre j) → ComplexPoint Q))
      [MemTrivializationAtlas e] : e.IsLinear ℂ := by
    exact MemTrivializationAtlas.out (e := e)
  refine { trivialization_linear' := hlinear, continuousOn_coordChange' := ?_ }
  intro e e' he he'
  letI := hlinear e
  letI := hlinear e'
  exact i1_linearChartTransition_continuousOn k (i1_normalFibre j) e e'

end HodgeLean.Foundations.BundleThom

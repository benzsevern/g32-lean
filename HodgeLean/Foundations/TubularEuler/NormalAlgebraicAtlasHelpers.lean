import HodgeLean.Foundations.BundleThom.NormalAtlasConstructionHelpers

/-! # The subatlas of actual algebraic normal frames

The fibre and total topologies are retained while atlas membership records a selected frame.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

variable (frames : ∀ x : ComplexPoint Q, Σ U : Q.left.Opens,
  {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
    SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) // x ∈ Point.overOpen U})

def normalFramedFiberBundle : FiberBundle (Fin k → ℂ) (i1_normalFibre j) where
  totalSpaceMk_isInducing' := (i1_normalFiberBundle j k frames).totalSpaceMk_isInducing'
  trivializationAtlas' := Set.range (fun x : ComplexPoint Q =>
    i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1)
  trivializationAt' x := i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1
  mem_baseSet_trivializationAt' x := (frames x).2.2
  trivialization_mem_atlas' x := ⟨x, rfl⟩

theorem normalFramedVectorBundle :
    letI := normalFramedFiberBundle j k frames
    VectorBundle ℂ (Fin k → ℂ) (i1_normalFibre j) := by
  letI := normalFramedFiberBundle j k frames
  have hlinear (e : Trivialization (Fin k → ℂ)
      (π (Fin k → ℂ) (i1_normalFibre j))) [MemTrivializationAtlas e] : e.IsLinear ℂ := by
    obtain ⟨x, rfl⟩ := (show e ∈ Set.range (fun x : ComplexPoint Q =>
      i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1) from
        MemTrivializationAtlas.out)
    exact i1_normalFrameTrivialization_isLinear j k (frames x).1 (frames x).2.1
  refine { trivialization_linear' := hlinear, continuousOn_coordChange' := ?_ }
  intro e e' he he'
  letI := hlinear e
  letI := hlinear e'
  exact i1_linearChartTransition_continuousOn k (i1_normalFibre j) e e'

#print axioms normalFramedFiberBundle
#print axioms normalFramedVectorBundle

end HodgeLean.Foundations.TubularEuler

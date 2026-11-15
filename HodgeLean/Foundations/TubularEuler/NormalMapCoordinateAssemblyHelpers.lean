import HodgeLean.Foundations.TubularEuler.NormalCoordinatePatchInverseHelpers

/-! # Local normal maps assembled from primitive analytic coordinates

The supplied ambient map is retained and the local inverses are constructed from its derivatives.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Bundle
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

def localNormalMapOfCoordinatePatches
    (U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    (m : C(U, ComplexPoint (Over.mk (v ≫ W.hom))))
    (hzero : ∀ x, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ U)
    (hmzero : ∀ x hx, m ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, hx⟩ =
      Point.map (i1_smoothLift ι v j hj) x)
    (patches : ∀ x, NormalCoordinatePatch ι k v j U m x) : LocalNormalMap ι k v j hj where
  domain := U
  map := m
  contains_zero := hzero
  map_zero := hmzero
  localInverse x := (patches x).localInverse
  local_zero x := (patches x).localInverse_zero
  local_domain x z hz := (patches x).localInverse_domain z hz
  local_map x z hz := (patches x).localInverse_map z hz
  local_support x z hz := ((patches x).localInverse_geometry z hz).2.2.2.2.1
  localCharts := by
    intro x z hz
    obtain ⟨hzb, hze, hza, _, _, hcz, hcf, hcg, A, hA⟩ :=
      (patches x).localInverse_geometry z hz
    exact ⟨(patches x).baseChart, (patches x).frame, (patches x).ambientChart,
      (patches x).base_hol, (patches x).frame_linear, (patches x).ambient_hol,
      hzb, hze, hza, (patches x).support, hcz, hcf, hcg, A, hA⟩

#print axioms localNormalMapOfCoordinatePatches

end HodgeLean.Foundations.TubularEuler

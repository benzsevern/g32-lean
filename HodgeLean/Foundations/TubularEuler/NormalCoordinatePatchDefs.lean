import HodgeLean.Foundations.TubularEuler.TubeDefs
import HodgeLean.Foundations.TubularEuler.AnalyticNormalInverseHelpers

/-! # Primitive coordinates of a supplied ambient normal map

The data retain the map, chart domains, analytic coordinate function, and actual transverse derivative.
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
variable (j : Q.left ⟶ V) [IsClosedImmersion j]
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Analytic coordinate functions of the supplied map, before inverse construction.
Source: Mathlib, `ContDiffAt.toOpenPartialHomeomorph` and `OpenPartialHomeomorph.contDiffAt_symm`;
Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24.
HC no distance; AV milestone no distance. -/
structure NormalCoordinatePatch
    (U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
    (m : C(U, ComplexPoint (Over.mk (v ≫ W.hom)))) (x : ComplexPoint Q) where
  baseChart : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ)
  frame : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j))
  ambientChart : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ))
  base_hol : a3b4_IsHolChart Q.hom (baseChart.trans
    ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph))
  frame_linear : frame.IsLinear ℂ
  ambient_hol : a3b4_IsHolChart W.hom ambientChart
  base_mem : x ∈ baseChart.source
  frame_mem : zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ frame.source
  support : ∀ y ∈ ambientChart.source,
    y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ (ambientChart y).2 = 0
  modelSource : Opens ((Fin k → ℂ) × (Fin k → ℂ))
  modelMap : ((Fin k → ℂ) × (Fin k → ℂ)) → ((Fin k → ℂ) × (Fin k → ℂ))
  model_mem : (baseChart x, (0 : Fin k → ℂ)) ∈ modelSource
  model_analytic : ContDiffOn ℝ ⊤ modelMap modelSource
  model_fix : ∀ b, (b, (0 : Fin k → ℂ)) ∈ modelSource → modelMap (b, 0) = (b, 0)
  model_transverse : ∀ b, (b, (0 : Fin k → ℂ)) ∈ modelSource →
    ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
      HasFDerivAt (fun w : Fin k → ℂ => (modelMap (b, w)).2) A.toContinuousLinearMap 0
  model_target : Set.MapsTo modelMap modelSource ambientChart.target
  frame_target : (modelSource : Set ((Fin k → ℂ) × (Fin k → ℂ))) ⊆
    (frame.toOpenPartialHomeomorph.trans
      (baseChart.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).target
  map_domain : ∀ q ∈ modelSource,
    (frame.toOpenPartialHomeomorph.trans
      (baseChart.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm q ∈ U
  map_agreement : ∀ q (hq : q ∈ modelSource), ambientChart.symm (modelMap q) =
    Point.map (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W)
      (m ⟨(frame.toOpenPartialHomeomorph.trans
        (baseChart.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm q, map_domain q hq⟩)

end HodgeLean.Foundations.TubularEuler

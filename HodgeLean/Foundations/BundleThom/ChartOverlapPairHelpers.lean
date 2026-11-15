import HodgeLean.Foundations.BundleThom.ChartProductPairHelpers

/-! # Actual overlap pair maps and varying normal coordinates

Inverse source-chart coordinates define maps into the target chart with the supplied base retained.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B T : Type} [TopologicalSpace B] [TopologicalSpace T] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ] [e'.IsLinear ℂ]

/-- Actual product coordinates over the overlap map into the supplied target chart pair.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, overlap comparisons. -/
def i1_chartOverlapProductPairMap (f : T → ↥(e.baseSet ∩ e'.baseSet)) (hf : Continuous f) :
    i1_productNormalPair T k ⟶ i1_chartPair k E e' :=
  i1_chartProductPairMap k E e e' (fun t => (f t).1) (continuous_subtype_val.comp hf)
    (fun t => (f t).2.1) (fun t => (f t).2.2)

/-- The actual target chart normal map is the varying transition matrix in source product coordinates.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex transition coordinates. -/
theorem i1_chartOverlapProductPairMap_comp_normal
    (f : T → ↥(e.baseSet ∩ e'.baseSet)) (hf : Continuous f) :
    i1_chartOverlapProductPairMap k E e e' f hf ≫ i1_chartNormal k E e' =
      i1_productMatrixNormalMap k (fun t => i1_chartTransitionMatrix k E e e' (f t))
        ((i1_chartTransitionMatrix_continuous k E e e').comp hf)
        (fun t => i1_chartTransitionMatrix_det_ne_zero k E e e' (f t)) := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact ((i1_chartTransitionMatrix_mulVec k E e e' (f p.1.1) p.1.2).trans
      (e.coordChangeL_apply e' (f p.1.1).2 p.1.2)).symm
  · apply ConcreteCategory.hom_ext
    intro p
    exact ((i1_chartTransitionMatrix_mulVec k E e e' (f p.1) p.2).trans
      (e.coordChangeL_apply e' (f p.1).2 p.2)).symm

end HodgeLean.Foundations.BundleThom

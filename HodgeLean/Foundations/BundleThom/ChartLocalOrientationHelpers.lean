import HodgeLean.Foundations.BundleThom.ChartTransitionMatrixHelpers

/-! # Local normal pullback comparison for actual complex charts

The comparison retains the supplied charts, their actual overlap and the coordinate transition matrix.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- On a neighbourhood in the actual chart overlap, its varying transition preserves every normal coclass pullback.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local complex Thom orientation. -/
theorem i1_chartTransition_locally_normal_pullback
    {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] (b : ↥(e.baseSet ∩ e'.baseSet)) :
    ∃ U : Opens ↥(e.baseSet ∩ e'.baseSet), b ∈ U ∧
      ∀ (n : ℕ) (u : RelativeCohomology ℚ (puncturedPair ℂ k) n),
        relativeCohomologyMap ℚ n
          (i1_productMatrixNormalMap k (fun x : U => i1_chartTransitionMatrix k E e e' x.1)
            ((i1_chartTransitionMatrix_continuous k E e e').comp continuous_subtype_val)
            (fun x => i1_chartTransitionMatrix_det_ne_zero k E e e' x.1)) u =
          relativeCohomologyMap ℚ n (i1_productNormalProjection U k) u :=
  i1_productMatrixNormalMap_locally_pullback k (i1_chartTransitionMatrix k E e e')
    (i1_chartTransitionMatrix_continuous k E e e')
    (i1_chartTransitionMatrix_det_ne_zero k E e e') b

end HodgeLean.Foundations.BundleThom

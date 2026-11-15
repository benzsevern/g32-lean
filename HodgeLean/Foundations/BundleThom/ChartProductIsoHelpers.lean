import HodgeLean.Foundations.BundleThom.ContractibleProductCoclassHelpers
import HodgeLean.Foundations.BundleThom.ThomChartFibreHelpers

/-! # Actual product-pair coordinates on supplied bundle charts

The isomorphism retains the chart's actual source topology and the exact nonzero-vector subspace.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- The actual chart pair is isomorphic to the product normal pair over its actual base domain.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, bundle trivializations as relative product coordinates. -/
def i1_chartPairProductIso : i1_chartPair k E e ≅ i1_productNormalPair e.baseSet k :=
  TopPair.isoOfSubset e.sourceHomeomorphBaseSetProd (by
    intro v
    change (e.sourceHomeomorphBaseSetProd v).2 ≠ 0 ↔ v.1.2 ≠ 0
    rw [e.sourceHomeomorphBaseSetProd_apply]
    apply not_congr
    change (e.continuousLinearEquivAt ℂ v.1.proj (e.mem_source.mp v.2)) v.1.2 = 0 ↔ _
    constructor
    · intro h
      apply (e.continuousLinearEquivAt ℂ v.1.proj (e.mem_source.mp v.2)).injective
      simpa only [map_zero] using h
    · intro h
      rw [h, map_zero])

/-- The product normal projection is the specified chart normal map under the actual chart pair isomorphism.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex normal coordinates. -/
theorem i1_chartPairProductIso_comp_projection :
    (i1_chartPairProductIso k E e).hom ≫ i1_productNormalProjection e.baseSet k =
      i1_chartNormal k E e := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Actual chart relative homology vanishes off twice the complex rank when the chart base domain is contractible.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative product homology. -/
theorem i1_contractibleChartRelativeHomology_isZero [ContractibleSpace e.baseSet]
    (n : ℕ) (hn : n ≠ 2 * k) : IsZero (RelativeHomology ℚ (i1_chartPair k E e) n) :=
  (i1_contractibleProductNormalRelativeHomology_isZero (B := e.baseSet) k n hn).of_iso
    ((relativeHomologyFunctor ℚ n).mapIso (i1_chartPairProductIso k E e))

end HodgeLean.Foundations.BundleThom

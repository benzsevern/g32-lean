import HodgeLean.Foundations.Program.G32Native.CoefficientNormalChartMatrix
import HodgeLean.Foundations.Program.G32Native.CoefficientModelChartNormalization
import HodgeLean.Foundations.BundleThom.ImmersionDefs

/-! # The original coefficient map factored through each model coordinate open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle TopologicalSpace
open HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native
variable (G : CanonicalAbelGeometry) (D : CoefficientNormalIdentification G)
local instance (x : ComplexPoint G.Q) : TopologicalSpace (i1_normalFibre G.ι.left x) :=
  i1_normalFibreTopology G.ι.left x
local instance : TopologicalSpace (TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left)) :=
  i1_normalTotalTopology G.ι.left G.k
variable [FiberBundle (Fin G.k → ℂ) (i1_normalFibre G.ι.left)]
variable [VectorBundle ℂ (Fin G.k → ℂ) (i1_normalFibre G.ι.left)]
variable (e : Trivialization (Fin G.k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left) → ComplexPoint G.Q))
variable [e.IsLinear ℂ]

/-- The analytic chart base restricted to the specified projective coordinate open. -/
def coefficientNormalChartBaseOpen (j : Fin (G.k + 1)) : Opens e.baseSet :=
  ⟨{b | normalPermutationBaseHomeomorph G.k (Equiv.swap 0 j)
      (coefficientBaseHomeomorph G b.1) ∈ Set.range (normalProjectiveChart G.k)},
    (isOpen_normalProjectiveChart_range G.k).preimage
      ((normalPermutationBaseHomeomorph G.k (Equiv.swap 0 j)).continuous.comp
        ((coefficientBaseHomeomorph G).continuous.comp continuous_subtype_val))⟩

/-- The original coefficient pair map in inverse analytic chart coordinates. -/
def coefficientNormalChartComposite (j : Fin (G.k + 1)) :
    i1_productNormalPair (coefficientNormalChartBaseOpen G e j) G.k ⟶
      TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace G.k)) {w | w.1.2 = 0}ᶜ :=
  i1_productBaseMap G.k
    (Subtype.val : coefficientNormalChartBaseOpen G e j → e.baseSet) continuous_subtype_val ≫
    (i1_chartPairProductIso G.k (i1_normalFibre G.ι.left) e).inv ≫
      i1_chartInclusion G.k (i1_normalFibre G.ι.left) e ≫ coefficientNormalPairMap G D

/-- The composite uses the original normal vector in the supplied analytic trivialization. -/
theorem coefficientNormalChartComposite_apply (j : Fin (G.k + 1))
    (bv : (coefficientNormalChartBaseOpen G e j) × (Fin G.k → ℂ)) :
    TopPair.Hom.fst (coefficientNormalChartComposite G D e j) bv =
      coefficientNormalTotalMap G D
        ⟨bv.1.1.1, (e.linearEquivAt ℂ bv.1.1.1 bv.1.1.2).symm bv.2⟩ := by
  exact congrArg (coefficientNormalTotalMap G D) (e.mk_symm bv.1.1.2 bv.2).symm

/-- The entire inverse analytic fibre lands in the same specified model coordinate open. -/
theorem coefficientNormalChartComposite_mem (j : Fin (G.k + 1))
    (bv : (coefficientNormalChartBaseOpen G e j) × (Fin G.k → ℂ)) :
    TopPair.Hom.fst (coefficientNormalChartComposite G D e j) bv ∈
      normalKernelCoclassChartOpen G.k j := by
  rw [coefficientNormalChartComposite_apply]
  change _ ∈ (normalCoordinateKernelChart G.k j).source
  rw [normalCoordinateKernelChart_source, normalCoordinateKernelParam_range]
  exact bv.1.2

/-- Lift the specified coefficient map to the actual model coordinate-open pair. -/
def coefficientNormalChartLift (j : Fin (G.k + 1)) :
    i1_productNormalPair (coefficientNormalChartBaseOpen G e j) G.k ⟶
      neighborhoodSupportComplementPair
        (normalKernelCoclassChartOpen G.k j : Set (ProjectiveNormalTotalSpace G.k))
        {w | w.1.2 = 0} :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun bv => ⟨TopPair.Hom.fst (coefficientNormalChartComposite G D e j) bv,
      coefficientNormalChartComposite_mem G D e j bv⟩,
      (TopPair.Hom.fst (coefficientNormalChartComposite G D e j)).hom.continuous.subtype_mk _⟩)
    (by
      intro bv hv hz
      change (TopPair.Hom.fst (coefficientNormalChartComposite G D e j) bv).val.2 = 0 at hz
      rw [coefficientNormalChartComposite_apply] at hz
      have hn := (coefficientNormalTotalMap_zero_iff G D _).mp hz
      exact hv ((e.linearEquivAt ℂ bv.1.1.1 bv.1.1.2).symm.map_eq_zero_iff.mp hn))

/-- The lift retains the literal original coefficient map on both parts of the pair. -/
theorem coefficientNormalChartLift_comp_inclusion (j : Fin (G.k + 1)) :
    coefficientNormalChartLift G D e j ≫ coefficientModelChartInclusion G.k j =
      coefficientNormalChartComposite G D e j := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

end HodgeLean.Foundations.Program.G32Native

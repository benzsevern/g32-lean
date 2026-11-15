import HodgeLean.Foundations.BundleResolution.ChernProductNormalThomHelpers
import HodgeLean.Foundations.BundleResolution.ChernDefs
import HodgeLean.Foundations.BundleThom.ChartProductIsoHelpers

/-! # Thom multiplication in actual linear bundle charts

The actual normalized chart class gives an isomorphism in every base degree,
using product coordinates on the specified chart source.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ)
  (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ]

def i1_chartBaseProjection : (i1_chartPair k E.fibre e).fst ⟶ TopCat.of e.baseSet :=
  TopCat.ofHom ⟨fun v => ⟨v.val.proj, e.mem_source.mp v.property⟩,
    ((FiberBundle.continuous_proj (Fin k → ℂ) E.fibre).comp continuous_subtype_val).subtype_mk _⟩

def i1_chartThomMultiplication (n : ℕ) :
    Cohomology ℚ (TopCat.of e.baseSet) n →ₗ[ℚ]
      RelativeCohomology ℚ (i1_chartPair k E.fibre e) (2 * k + n) :=
  (i1_relativeCup (i1_chartPair k E.fibre e) (2 * k) n
    (i1_chartOrientation k E.fibre e)).comp
      (cohomologyMap ℚ n (i1_chartBaseProjection E e))

theorem i1_chartThomMultiplication_product (n : ℕ)
    (α : Cohomology ℚ (TopCat.of e.baseSet) n) :
    relativeCohomologyMap ℚ (2 * k + n) (i1_chartPairProductIso k E.fibre e).hom
      (i1_productNormalThomMultiplication k (TopCat.of e.baseSet) n α) =
        i1_chartThomMultiplication E e n α := by
  have hn : relativeCohomologyMap ℚ (2 * k) (i1_chartPairProductIso k E.fibre e).hom
      (relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection e.baseSet k)
        (HodgeLean.RealDefs.normalizedPointCoclass k)) = i1_chartOrientation k E.fibre e := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      i1_chartPairProductIso_comp_projection]
    rfl
  have hb : TopPair.Hom.fst (i1_chartPairProductIso k E.fibre e).hom ≫
      HodgeLean.Foundations.Singular.productFirst (TopCat.of e.baseSet)
        (TopCat.of (Fin k → ℂ)) = i1_chartBaseProjection E e := by
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    change (e.sourceHomeomorphBaseSetProd v).1.val = v.val.proj
    rw [e.sourceHomeomorphBaseSetProd_apply]
  have hbc : cohomologyMap ℚ n (TopPair.Hom.fst (i1_chartPairProductIso k E.fibre e).hom)
      (cohomologyMap ℚ n (HodgeLean.Foundations.Singular.productFirst
        (TopCat.of e.baseSet) (TopCat.of (Fin k → ℂ))) α) =
      cohomologyMap ℚ n (i1_chartBaseProjection E e) α := by
    have h := congrArg (fun l => l α) (cohomologyMap_comp ℚ n
      (TopPair.Hom.fst (i1_chartPairProductIso k E.fibre e).hom)
      (HodgeLean.Foundations.Singular.productFirst
        (TopCat.of e.baseSet) (TopCat.of (Fin k → ℂ))))
    exact h.symm.trans (congrArg (fun f => cohomologyMap ℚ n f α) hb)
  simp only [i1_productNormalThomMultiplication, i1_chartThomMultiplication,
    LinearMap.comp_apply]
  exact (i1_relativeCup_naturality (i1_chartPairProductIso k E.fibre e).hom
    (2 * k) n _ _).trans
    (congrArg₂ (fun u v => i1_relativeCup (i1_chartPair k E.fibre e)
      (2 * k) n u v) hn hbc)

theorem i1_chartThomMultiplication_bijective (n : ℕ) :
    Function.Bijective (i1_chartThomMultiplication E e n) := by
  have hi : Function.Bijective (relativeCohomologyMap ℚ (2 * k + n)
      (i1_chartPairProductIso k E.fibre e).hom) := by
    constructor
    · exact i1_relativeCohomologyMap_iso_injective _ _
    · intro y
      refine ⟨relativeCohomologyMap ℚ (2 * k + n)
        (i1_chartPairProductIso k E.fibre e).inv y, ?_⟩
      rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
        Iso.hom_inv_id, relativeCohomologyMap_id, LinearMap.id_apply]
  have h := hi.comp (i1_productNormalThomMultiplication_bijective k (TopCat.of e.baseSet) n)
  have he : i1_chartThomMultiplication E e n =
      (relativeCohomologyMap ℚ (2 * k + n) (i1_chartPairProductIso k E.fibre e).hom).comp
        (i1_productNormalThomMultiplication k (TopCat.of e.baseSet) n) := by
    ext α
    exact (i1_chartThomMultiplication_product E e n α).symm
  rw [he]
  exact h

end HodgeLean.Foundations.BundleResolution

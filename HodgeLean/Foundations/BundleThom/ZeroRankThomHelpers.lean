import HodgeLean.Foundations.BundleThom.Defs

/-! # The normalized class for zero-rank complex bundles

Every actual fibre is zero, so the relative class is the degree-zero augmentation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin 0 → ℂ) E)]
variable [FiberBundle (Fin 0 → ℂ) E] [VectorBundle ℂ (Fin 0 → ℂ) E]

/-- Every actual fibre vector of a rank-zero complex bundle is zero.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, rank-zero bundles. -/
theorem i1_zeroRankFibre_eq_zero (b : B) (v : E b) : v = 0 := by
  let e := trivializationAt (Fin 0 → ℂ) E b
  let L := e.continuousLinearEquivAt ℂ b (FiberBundle.mem_baseSet_trivializationAt _ _ _)
  exact L.injective (Subsingleton.elim _ _)

/-- The actual zero support of a rank-zero bundle is the entire total space.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
theorem i1_zeroRankSupport_eq_univ : i1_zeroSupport 0 E = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact i1_zeroRankFibre_eq_zero E z.proj z.2

/-- The complement pair of the rank-zero zero section has empty subspace.
Source: Hatcher, Algebraic Topology, §3.1, pairs with empty subspace. -/
theorem i1_zeroRankComplement_isEmpty :
    IsEmpty (TopPair.ofSubset (X := i1_totalSpace 0 E) (i1_zeroSupport 0 E)ᶜ).snd :=
  ⟨fun z => z.2 (i1_zeroRankFibre_eq_zero E z.1.proj z.1.2)⟩

/-- The actual zero-rank bundle class is the constant augmentation coclass.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, zero-rank Thom normalization. -/
def i1_zeroRankThom : i1_supportedClass 0 E := by
  let P := TopPair.ofSubset (X := i1_totalSpace 0 E) (i1_zeroSupport 0 E)ᶜ
  letI : IsIso (relativeChainProjection ℚ P) :=
    isIso_relativeChainProjection P (i1_zeroRankComplement_isEmpty E)
  exact augmentationClass P

/-- Every rank-zero complex chart has empty punctured subspace.
Source: Hatcher, Algebraic Topology, §3.1, pairs with empty subspace. -/
theorem i1_zeroRankChartComplement_isEmpty
    (e : Trivialization (Fin 0 → ℂ) (TotalSpace.proj : TotalSpace (Fin 0 → ℂ) E → B))
    [e.IsLinear ℂ] : IsEmpty (i1_chartPair 0 E e).snd :=
  ⟨fun z => z.2 (i1_zeroRankFibre_eq_zero E z.1.1.proj z.1.1.2)⟩

/-- The zero-rank augmentation class has the prescribed normalization in every actual complex chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, zero-rank Thom normalization. -/
theorem i1_zeroRankThom_chart
    (e : Trivialization (Fin 0 → ℂ) (TotalSpace.proj : TotalSpace (Fin 0 → ℂ) E → B))
    [e.IsLinear ℂ] :
    relativeCohomologyMap ℚ 0 (i1_chartInclusion 0 E e) (i1_zeroRankThom E) =
      i1_chartOrientation 0 E e := by
  let P := TopPair.ofSubset (X := i1_totalSpace 0 E) (i1_zeroSupport 0 E)ᶜ
  letI : IsIso (relativeChainProjection ℚ P) :=
    isIso_relativeChainProjection P (i1_zeroRankComplement_isEmpty E)
  letI : IsIso (relativeChainProjection ℚ (i1_chartPair 0 E e)) :=
    isIso_relativeChainProjection _ (i1_zeroRankChartComplement_isEmpty E e)
  change relativeCohomologyMap ℚ 0 (i1_chartInclusion 0 E e) (augmentationClass P) = _
  rw [relativeCohomologyMap_augmentationClass, i1_chartOrientation,
    normalizedPointCoclass_zero, relativeCohomologyMap_augmentationClass]

end HodgeLean.Foundations.BundleThom

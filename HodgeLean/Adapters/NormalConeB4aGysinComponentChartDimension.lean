import HodgeLean.Adapters.NormalConeB4aGysinIntegralSmoothDimension
import HodgeLean.Adapters.NormalConeB4aGysinSmoothSourceDimension
import HodgeLean.Adapters.NormalConeB4aClassComponentDensity
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every reduced integral component meeting a holomorphic ambient chart has
dimension bounded by that chart's parameter-plus-normal dimension. -/
theorem a3b4a_gysin_component_dimension_in_chart
    (X : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (ξ : X.left) {n c : ℕ}
    (Φ : OpenPartialHomeomorph (ComplexPoint X) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart X.hom Φ)
    (x : ComplexPoint X) (hx : x ∈ Φ.source)
    (hxξ : x.underlying ∈ closure ({ξ} : Set X.left)) :
    topologicalKrullDim (cycleComponent X.left ξ) ≤ (n + c : ℕ) := by
  let C := Over.mk (cycleComponentι X.left ξ ≫ X.hom)
  let i : C ⟶ X := Over.homMk (cycleComponentι X.left ξ) rfl
  letI : IsIntegral C.left := inferInstanceAs (IsIntegral (cycleComponent X.left ξ))
  letI : LocallyOfFiniteType C.hom :=
    inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left ξ ≫ X.hom))
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (cycleComponentι X.left ξ))
  letI : IsSeparated C.hom :=
    inferInstanceAs (IsSeparated (cycleComponentι X.left ξ ≫ X.hom))
  letI : NoetherianSpace C.left := i.left.isClosedEmbedding.isInducing.noetherianSpace
  have hxrange : x ∈ Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm X C i]
    change x.underlying ∈ Set.range (cycleComponentι X.left ξ)
    rwa [range_cycleComponentι]
  obtain ⟨z, hz⟩ := hxrange
  let A := C.hom.smoothLocus
  letI : Nonempty A :=
    ⟨⟨genericPoint C.left, C.hom.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have hdense := HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen C A
  have hO : IsOpen (Point.map i ⁻¹' Φ.source) :=
    Φ.open_source.preimage (Point.continuous_map i)
  have hzO : z ∈ Point.map i ⁻¹' Φ.source := by
    change Point.map i z ∈ Φ.source
    rwa [hz]
  obtain ⟨w, hwA, hwO⟩ := hdense.inter_nhds_nonempty (hO.mem_nhds hzO)
  letI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  letI : Smooth (A.ι ≫ C.hom) := C.hom.smooth_restrict_smoothLocus
  obtain ⟨d, hd⟩ := Smooth.exists_smoothOfRelativeDimension (A.ι ≫ C.hom)
  letI : SmoothOfRelativeDimension d (A.ι ≫ C.hom) := hd
  let S := ComplexPoint.openScheme C A
  let j : S ⟶ C := ComplexPoint.openInclusion C A
  let g : S ⟶ X := j ≫ i
  letI : SmoothOfRelativeDimension d S.hom := hd
  letI : LocallyOfFiniteType S.hom := inferInstanceAs (LocallyOfFiniteType (A.ι ≫ C.hom))
  letI : NoetherianSpace A.toScheme := A.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace S.left := inferInstanceAs (NoetherianSpace A.toScheme)
  letI : QuasiCompact S.hom := inferInstance
  letI : IsSeparated S.hom := inferInstanceAs (IsSeparated (A.ι ≫ C.hom))
  letI : Mono i := Over.mono_of_mono_left i
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion A.ι)
  letI : Mono j := Over.mono_of_mono_left j
  let wa := (ComplexPoint.openHomeomorph C A).symm ⟨w, hwA⟩
  have hwmap : Point.map j wa = w :=
    congrArg Subtype.val ((ComplexPoint.openHomeomorph C A).apply_symm_apply ⟨w, hwA⟩)
  have hgw : Point.map g wa = Point.map i w := by
    simpa only [Point.map, g, Category.assoc] using congrArg (Point.map i) hwmap
  have hdchart : d ≤ n + c := a3b4a_gysin_smooth_source_chart_dimension_le
    S X d n c g (ComplexPoint.map_injective_of_mono g) Φ hΦ wa (by rwa [hgw])
  exact (a3b4a_gysin_integral_dimension_bound_of_smooth_open C A d).trans
    (by exact_mod_cast hdchart)

end HodgeLean.Adapters

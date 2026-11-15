import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CommonComponentPhase
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralBinomialChartOrder
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralChartSliceDeck
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralBinomialEigenvalues
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedAffineDeck
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentDeckExtension
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedSphereProjection
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialLabelledDeck
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialPhaseNormalization
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PrimitiveChartOrder
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualReciprocalEndpointSections
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationComplementarySliceCoordinates
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralReciprocalSliceChartData
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CanonicalReciprocalIntegralPair
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralChartSliceRatio
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralCoefficientPointRestriction
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentsProofs
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalDoubleBinomialCharts
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationSliceCoordinates
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralReciprocalSliceMaps
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualReciprocalChartSections
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralIntegralCoefficientSlice
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CanonicalBinomialIdentities
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalIntegralParameters
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RootLabelRelabelling
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalSelectorValues
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalBinomialExponents
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RetainedModelInclusion
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartCoefficientSquares
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralUnitPowerZero
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedSphereEndpoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The specified original generic deck symmetry retains the actual component morphisms, their common phase, projection and exact scheme order. -/
theorem regular_pair_binomial_deck_coordinates
    {L : Type} [Field L]
    (Bbase Xbase : Over (Spec ↧ℂ)) [IsIntegral Bbase.left] [IsSeparated Bbase.hom]
    [IsIntegral Xbase.left] [IsProjective Xbase.hom]
    (p : Xbase ⟶ Bbase) (I₁ I₂ : Bbase.left.IdealSheafData)
    (hcartier : ∀ z : Xbase.left, ∃ V : Xbase.left.affineOpens, z ∈ V.1 ∧
      Nonempty ((((I₁ ⊔ I₂).comap p.left).ideal V) ≃ₗ[Γ(Xbase.left, V)] Γ(Xbase.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ Bbase),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty ((((I₁ ⊔ I₂).comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ Xbase, k ≫ p = f)
    (η : Spec ↧L ⟶ Xbase.left) [IsDominant η] [QuasiCompact η] [QuasiSeparated η]
    [IsProjective (s2b_normalizationOver Xbase η).hom]
    [IsFinite (s2b_normalizationMap Xbase η).left]
    (U : Bbase.left.affineOpens) [Nonempty U.1] (u v : Γ(Bbase.left, U))
    (hu : I₁.ideal U = Ideal.span {u}) (hv : I₂.ideal U = Ideal.span {v})
    (hvreg : IsRegular v) (hureg : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hureg' : IsRegular u) (hvreg' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (φ₀ : Γ(Bbase.left, U) →+* L)
    (κ : Bbase.left.functionField →+* L)
    (hφ : κ.comp (algebraMap Γ(Bbase.left, U) Bbase.left.functionField) = φ₀)
    (hηbase : η ≫ p.left = Spec.map (CommRingCat.ofHom φ₀) ≫ U.2.fromSpec)
    (m α : ℕ) (hm : 0 < m) (hα : α ≤ m)
    (hfield : letI := κ.toAlgebra
      Module.Finite Bbase.left.functionField L ∧ IsGalois Bbase.left.functionField L ∧
        IsCyclic (L ≃ₐ[Bbase.left.functionField] L) ∧ Module.finrank Bbase.left.functionField L = m)
    (δ₀ : letI := κ.toAlgebra; L ≃ₐ[Bbase.left.functionField] L)
    (hδorder : orderOf δ₀ = m)
    (dN : s2b_normalizationOver Xbase η ⟶ s2b_normalizationOver Xbase η)
    (hdN : dN ≫ s2b_normalizationMap Xbase η = s2b_normalizationMap Xbase η)
    (hδN : Spec.map (CommRingCat.ofHom δ₀.toRingHom) ≫ η.toNormalization =
      η.toNormalization ≫ dN.left)
    (hperiod : (End.of dN) ^ m = 1)
    (ε : Γ(Bbase.left, U)ˣ) (t : L) (hu0 : φ₀ u ≠ 0) (hv0 : φ₀ v ≠ 0) (ht : t ≠ 0)
    (htgen : Subfield.closure (Set.range φ₀ ∪ {t}) = ⊤)
    (hteq : t ^ m = φ₀ ε * φ₀ u ^ α * φ₀ v ^ (m - α))
    (Ncoords : ℕ) (z : Fin Ncoords → Γ(Bbase.left, U)) (a₀ a₁ : Fin Ncoords)
    (ha : a₀ ≠ a₁) (hza : u = z a₀) (hzb : v = z a₁)
    (hzet : (MvPolynomial.eval₂Hom (Bbase.hom.appLE ⊤ U.1 le_top).hom z).Etale)
    (x : ComplexPoint Bbase) (hxU : x.left (IsLocalRing.closedPoint ℂ) ∈ U.1)
    (hx₁ : x.left (IsLocalRing.closedPoint ℂ) ∈ I₁.support)
    (hx₂ : x.left (IsLocalRing.closedPoint ℂ) ∈ I₂.support) :
    let β := s2b_normalizationMap Xbase η
    let F := coveringSlice β p x
    let E := exceptionalSlice p x
    let P := sliceProjection β p x
    let A := pullback.fst p x
    ∃ (j : ZMod (Nat.gcd m α) → (projectiveLine ⟶ F))
      (vE : ComplexPoint E ≃ₜ OnePoint ℂ) (c : ℂ) (hc : c ≠ 0),
      c ^ m = 1 ∧
      (∀ l, IsClosedImmersion (j l).left) ∧
      (∀ z : ComplexPoint F, ∃! l, z ∈ Set.range (Point.map (j l))) ∧
      (∀ l z, Point.map (sliceDeck β p x dN hdN)
          (Point.map (j l) (lineCoordinate.symm z)) =
        Point.map (j (l + 1)) (lineCoordinate.symm
          ((Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc)) z))) ∧
      (∀ l z, vE (Point.map P (Point.map (j l) (lineCoordinate.symm z))) =
        projection m α c (l, z)) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (s2c_strictTransform p.left I₁ (I₁ ⊔ I₂)).support ↔ vE z = ((0 : ℂ) : OnePoint ℂ))) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (s2c_strictTransform p.left I₂ (I₁ ⊔ I₂)).support ↔ vE z = (∞ : OnePoint ℂ))) ∧
      orderOf (End.of (sliceDeck β p x dN hdN)) = m := by
  obtain ⟨M, π, eM, j₁, j₂, hj₁, hj₂, heM, hπ₁, hπ₂, hcover, hoverlap, hoverlap',
    j, F, hjdef, hjopen, hFinj, hjbase, hFc, hFr, _, _, _, hFj, EN, wN,
    hEN, hENb, hwN, heqN, hgenN, zA, b₀, b₁, hb, hzb₀, hzb₁, hzA,
    jBraw, G, hjBraw, hjBopen, hGinj, hjBbaseRaw, hGc, hGr, hGjRaw,
    wB, hwB, heqB, hgenBRaw, zB, b₂, b₃, hbB, hzb₂, hzb₃, hzB⟩ :=
    original_double_binomial_charts (L := L) Bbase Xbase p
      (I₁) (I₂)
      hcartier hblowup U u v hu hv hvreg hureg hureg' hvreg'
      η φ₀ hηbase m α hm hα ε t hu0 hv0 ht htgen hteq
      Ncoords z a₀ a₁ ha hza hzb hzet
  letI := s2e_step1_sectionAlgebra Bbase U.1
  haveI : Nonempty U.1 := ⟨⟨x.left (IsLocalRing.closedPoint ℂ), hxU⟩⟩
  let K := Bbase.left.functionField
  letI : Algebra K L := κ.toAlgebra
  haveI : Module.Finite K L := hfield.1
  haveI : IsGalois K L := hfield.2.1
  haveI : IsCyclic (L ≃ₐ[K] L) := hfield.2.2.1
  have hdegree : Module.finrank K L = m := hfield.2.2.2
  let R := Γ(Bbase.left, U)
  let A := RegularPairChart.ring u v
  letI : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen Bbase.left U.1 U.2
  have hvK : algebraMap R K v ≠ 0 := by
    intro hvK
    have h := DFunLike.congr_fun hφ v
    change κ (algebraMap R K v) = φ₀ v at h
    rw [hvK, map_zero] at h
    exact hv0 h.symm
  obtain ⟨H, hHc, hHr, hHF, hfraction, hRtower, hAtower⟩ :=
    original_chart_fraction_field (R := R) (K := K) (L := L) u v κ F (hFc.trans hφ.symm) hFinj hvK
  letI : Algebra A K := H.toAlgebra
  letI : Algebra A L := F.toAlgebra
  haveI : IsFractionRing A K := hfraction
  haveI : IsScalarTower A K L := hAtower
  letI : Algebra ℂ L := (F.comp (algebraMap ℂ A)).toAlgebra
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr hFinj
  haveI : IsDomain A := IsDomain.of_faithfulSMul A L
  let eC := (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv
  let cE : MvPolynomial (Fin Ncoords) ℂ →ₐ[ℂ] A := MvPolynomial.aeval zA
  have hcE : cE.toRingHom.Etale :=
    etale_coordinate_coefficient_equiv eC
      ((RegularPairChart.coeff u v).comp (Bbase.hom.appLE ⊤ U.1 le_top).hom) zA hzA
  have hcEX : cE (MvPolynomial.X b₀) = RegularPairChart.ratio u v := by
    exact (MvPolynomial.aeval_X zA b₀).trans hzb₀
  have hw0 : (wN : L) ≠ 0 := by rw [hwN]; exact div_ne_zero ht hv0
  have hwBin : (wN : L) ^ m = algebraMap A L (RegularPairChart.coeff u v ε) *
      (algebraMap A L (RegularPairChart.ratio u v)) ^ α := by
    have h := congrArg (fun q : normalizedChart F => (q : L)) heqN
    change (wN : L) ^ m = F (RegularPairChart.coeff u v ε * RegularPairChart.ratio u v ^ α) at h
    change (wN : L) ^ m = F (RegularPairChart.coeff u v ε) * F (RegularPairChart.ratio u v) ^ α
    simpa only [map_mul, map_pow] using h
  have hs : algebraMap A L (RegularPairChart.ratio u v) ≠ 0 := by
    change F (RegularPairChart.ratio u v) ≠ 0
    rw [hFr]
    exact div_ne_zero hu0 hv0
  obtain ⟨c, jO, φ, hc, hcopen, hjO, hjOsq, hxφ⟩ :=
    original_chart_over Bbase Xbase p U u v j hjbase x hxU
  haveI : IsOpenImmersion jO.left := hjO.symm ▸ hjopen
  haveI : IsOpenImmersion c.left := hcopen
  have hFjO : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ jO.left = η := by
    rw [hjO]
    exact hFj
  haveI : IsOpenImmersion j₁ := hj₁
  haveI : IsOpenImmersion j₂ := hj₂
  obtain ⟨vE, hEnds, hRatio⟩ := retained_base_ratio_sphere Bbase Xbase p
    U (I₁) (I₂)
    u v hu hv hvreg' hureg x hxU hx₁ hx₂ M π eM heM j₁ j₂ hπ₁ hπ₂ hcover hoverlap
  let D₂ := s2c_strictTransform p.left (I₂)
    (I₁ ⊔ I₂)
  have hrange : Set.range jO.left = (p.left ⁻¹ᵁ U.1 : Set Xbase.left) \ D₂.support := by
    rw [hjO, hjdef]
    exact compared_chart_image_complement p.left U
      (I₁) (I₂)
      u v hu hv hureg hvreg' M π eM heM j₁ j₂ hπ₁ hπ₂ hcover hoverlap
  haveI : IsDominant η.fromNormalization := by
    haveI : IsDominant (η.toNormalization ≫ η.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      infer_instance
    exact IsDominant.of_comp η.toNormalization η.fromNormalization
  haveI : IsDominant (s2b_normalizationMap Xbase η).left := by
    change IsDominant η.fromNormalization
    infer_instance
  haveI : Mono c.left := inferInstance
  haveI : Mono c := Over.mono_of_mono_left c
  have hβ := proper_dominant_complex_points_surjective (s2b_normalizationMap Xbase η)
  let δ : L ≃ₐ[K] L := δ₀
  have ho : orderOf δ = m := hδorder
  obtain ⟨ζ, hζ, hδw, q₁, t₁, κ₁, E₁, hq₁, ht₁, hκ₁, hκ₁0, hk₁, hE₁⟩ :=
    normalization_slice_binomial_coordinates (R := R) (K := K) (L := L) u v ε ε.isUnit
      Ncoords cE hcE b₀ hcEX m α hm hdegree (wN : L) hw0 hwBin hgenN hs δ ho
      Xbase Bbase η p x jO hFjO c hjOsq φ hxφ hβ D₂ vE
      (fun z => (hEnds z).2)
      (slice_chart_image_complement (s2b_normalizationMap Xbase η) p x U.1 hxU jO.left D₂ hrange)
      (by
        intro z y hy
        apply hRatio z y.left
        have hh := congrArg (fun q => q.left) hy
        change y.left ≫ jO.left = _ at hh
        rw [hjO, hjdef] at hh
        exact hh)
  obtain ⟨uM, huM, huMopen, huMb, huMrange⟩ :=
    retained_model_open_inclusion Bbase Xbase p U M π eM heM
  haveI : IsOpenImmersion uM.left := huMopen
  obtain ⟨k₁, hk₁M, hpoint₁⟩ := chart_coefficient_square_over u v M π j₁ hπ₁
  obtain ⟨k₂, hk₂M, hpoint₂⟩ := chart_coefficient_square_over v u M π j₂ hπ₂
  haveI : IsOpenImmersion k₁.left := by rw [hk₁M]; infer_instance
  haveI : IsOpenImmersion k₂.left := by rw [hk₂M]; infer_instance
  have hjk₁ : k₁ ≫ uM = jO := by
    apply Over.OverMorphism.ext
    change k₁.left ≫ uM.left = jO.left
    rw [hk₁M, huM, hjO, hjdef]
  let jB := k₂ ≫ uM
  haveI : IsOpenImmersion jB.left := by dsimp [jB]; infer_instance
  have hjBrawEq : jB.left = jBraw := by
    change k₂.left ≫ uM.left = jBraw
    rw [hk₂M, huM, hjBraw]
  have hjBbase := hjBrawEq ▸ hjBbaseRaw
  have hGj : Spec.map (CommRingCat.ofHom G) ≫ jB.left = η := by
    rw [hjBrawEq]
    exact hGjRaw
  let A₂ := RegularPairChart.ring v u
  have huK : algebraMap R K u ≠ 0 := by
    intro huK
    have hh := DFunLike.congr_fun hφ u
    change κ (algebraMap R K u) = φ₀ u at hh
    rw [huK, map_zero] at hh
    exact hu0 hh.symm
  obtain ⟨H₂, hH₂c, hH₂r, hH₂G, hfraction₂, hRtower₂, hA₂tower⟩ :=
    original_chart_fraction_field (R := R) (K := K) (L := L) v u κ G (hGc.trans hφ.symm) hGinj huK
  letI : Algebra A₂ K := H₂.toAlgebra
  letI : Algebra A₂ L := G.toAlgebra
  haveI : IsFractionRing A₂ K := hfraction₂
  haveI : IsScalarTower A₂ K L := hA₂tower
  haveI : IsScalarTower ℂ A₂ L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    change F (algebraMap ℂ A z) = G (algebraMap ℂ A₂ z)
    rw [← (regularPairCoefficientAlgHom u v).commutes z,
      ← (regularPairCoefficientAlgHom v u).commutes z]
    exact (DFunLike.congr_fun hFc (algebraMap ℂ R z)).trans
      (DFunLike.congr_fun hGc (algebraMap ℂ R z)).symm
  haveI : FaithfulSMul A₂ L := (faithfulSMul_iff_algebraMap_injective A₂ L).mpr hGinj
  haveI : IsDomain A₂ := IsDomain.of_faithfulSMul A₂ L
  have hwB0 : (wB : L) ≠ 0 := by rw [hwB]; exact div_ne_zero ht hu0
  have hgenB : Subfield.closure (Set.range (algebraMap A₂ L) ∪ {(wB : L)}) = ⊤ := hgenBRaw
  have hwBin₂ : (wB : L) ^ m = algebraMap A₂ L (RegularPairChart.coeff v u ε) *
      (algebraMap A₂ L (RegularPairChart.ratio v u)) ^ (m - α) := by
    have hh := congrArg (fun q : normalizedChart G => (q : L)) heqB
    change (wB : L) ^ m = G (RegularPairChart.coeff v u ε * RegularPairChart.ratio v u ^ (m - α)) at hh
    change (wB : L) ^ m = G (RegularPairChart.coeff v u ε) * G (RegularPairChart.ratio v u) ^ (m - α)
    simpa only [map_mul, map_pow] using hh
  have hs₂ : algebraMap A₂ L (RegularPairChart.ratio v u) ≠ 0 := by
    change G (RegularPairChart.ratio v u) ≠ 0
    rw [hGr]
    exact div_ne_zero hv0 hu0
  let cE₂ : MvPolynomial (Fin Ncoords) ℂ →ₐ[ℂ] A₂ := MvPolynomial.aeval zB
  have hcE₂ : cE₂.toRingHom.Etale := etale_coordinate_coefficient_equiv eC
    ((RegularPairChart.coeff v u).comp (Bbase.hom.appLE ⊤ U.1 le_top).hom) zB hzB
  have hcE₂X : cE₂ (MvPolynomial.X b₂) = RegularPairChart.ratio v u :=
    (MvPolynomial.aeval_X zB b₂).trans hzb₂
  have hjBsq : jB ≫ p = Over.homMk
      (Spec.map (CommRingCat.ofHom (regularPairCoefficientAlgHom v u).toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap (regularPairCoefficientAlgHom v u)) ≫ c := by
    apply Over.OverMorphism.ext
    change jB.left ≫ p.left = _ ≫ c.left
    rw [hc]
    exact hjBbase
  obtain ⟨vE₂, hEnds₂, hRatio₂⟩ := retained_base_ratio_sphere Bbase Xbase p
    U (I₂) (I₁)
    v u hv hu hureg hvreg' x hxU hx₂ hx₁ M π eM heM j₂ j₁ hπ₂ hπ₁
    (fun y => (hcover y).symm) hoverlap'
  let D₁ := s2c_strictTransform p.left (I₁)
    (I₂ ⊔ I₁)
  have hrange₂ : Set.range jB.left = (p.left ⁻¹ᵁ U.1 : Set Xbase.left) \ D₁.support := by
    change Set.range (k₂.left ≫ uM.left) = _
    rw [hk₂M, huM]
    exact compared_chart_image_complement p.left U
      (I₂) (I₁)
      v u hv hu hvreg' hureg M π eM heM j₂ j₁ hπ₂ hπ₁
      (fun y => (hcover y).symm) hoverlap'
  have hsecond := normalization_complementary_slice_binomial_coordinates (R := R) (K := K) (L := L) v u ε ε.isUnit
    Ncoords cE₂ hcE₂ b₂ hcE₂X m α hm hα hdegree (wB : L) hwB0 hwBin₂ hgenB hs₂ δ ho
    Xbase Bbase η p x jB hGj c hjBsq φ hxφ hβ D₁ vE₂
    (fun z => (hEnds₂ z).2)
    (slice_chart_image_complement (s2b_normalizationMap Xbase η) p x U.1 hxU jB.left D₁ hrange₂)
    (by
      intro z y hy
      apply hRatio₂ z y.left
      have hh := congrArg (fun q => q.left) hy
      change y.left ≫ jB.left = _ at hh
      change y.left ≫ (k₂.left ≫ uM.left) = _ at hh
      rw [hk₂M, huM] at hh
      exact hh)
  obtain ⟨hgcd, hred₂⟩ := reciprocal_binomial_exponents m α hm hα
  rw [hgcd] at hred₂
  simp only [hred₂] at hsecond
  obtain ⟨ζ₂, hζ₂, hδw₂, q₂, t₂, κ₂, E₂, hq₂, ht₂, hκ₂, hκ₂0, hk₂, hE₂⟩ := hsecond
  let g := Nat.gcd m α
  let n := m / g
  let a' := α / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left α hm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m α)) hg
  have ha' : a' ≤ n := Nat.div_le_div_right hα
  have hratioG : G (RegularPairChart.ratio v u) = (F (RegularPairChart.ratio u v))⁻¹ := by
    rw [hGr, hFr, inv_div]
  have hwBval : (wB : L) = (wN : L) / F (RegularPairChart.ratio u v) := by
    rw [hwB, hwN, hFr]
    dsimp only [dividedGenerator]
    field_simp
  have hq₂₁ : (q₂ : L) = (q₁ : L) := by
    rw [hq₂, hwBval]
    change ((wN : L) / F (RegularPairChart.ratio u v)) ^ n /
      G (RegularPairChart.ratio v u) ^ (n - a') = (q₁ : L)
    rw [hratioG]
    exact (reciprocal_binomial_selector_value n a' ha' (wN : L)
      (F (RegularPairChart.ratio u v)) hs).trans hq₁.symm
  obtain ⟨qB, sB, hqB, hsB, hqBu, hqBpow, hsBpow, hts⟩ := canonical_reciprocal_integral_pair
    φ₀ (RegularPairChart.coeff u v) (RegularPairChart.coeff v u) F G hFc hGc
    m α hm ε (RegularPairChart.ratio u v) (RegularPairChart.ratio v u) hs hratioG
    wN q₁ t₁ heqN hq₁ ht₁
  have hqBeq : qB = q₂ := Subtype.ext (hqB.trans hq₂₁.symm)
  have hq1B : (q₁ : L) = (qB : L) := hqB.symm
  have hcovM : ∀ y : (Over.mk (π ≫ ComplexPoint.affineSpecStructureMap R)).left,
      (∃ a, k₁.left a = y) ∨ ∃ b, k₂.left b = y := by
    intro y
    rw [hk₁M, hk₂M]
    exact hcover y
  have hfM : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ k₁.left ≫ uM.left = η := by
    change Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ (k₁ ≫ uM).left = _
    rw [hjk₁]
    exact hFjO
  obtain ⟨N, JN, lN, JA, JB, Q, T, hNint, hNlft, hJN, hJA, hJB, hlN,
    hJAbase, hJBbase, hJArange, hJBrange, hcovN, hQA, hQB, hTA, hTB, hpA, hpB⟩ :=
    literal_reciprocal_slice_maps (A := A) (B := A₂) (L := L) Xbase Bbase
      (Over.mk (π ≫ ComplexPoint.affineSpecStructureMap R)) p x η
      U.1 hxU uM huMrange k₁ k₂ hcovM
      hfM (by exact hGj) q₁ t₁ qB sB hq1B hts
  let βN := s2b_normalizationMap Xbase η
  let Fs := coveringSlice βN p x
  let Ps := sliceProjection βN p x
  let As := pullback.fst p x
  let aN := pullback.fst βN As
  haveI : IsOpenImmersion JN.left := hJN
  haveI : Mono JN := Over.mono_of_mono_left JN
  haveI : IsOpenImmersion JA.left := hJA
  haveI : IsOpenImmersion JB.left := hJB
  haveI : IsClosedImmersion As.left := s2v_schemeFibre_closedImmersion p x
  haveI : IsClosedImmersion aN.left := by
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (((IsPullback.of_hasPullback βN As).map (Over.forget _)).flip)
      (show IsClosedImmersion As.left from inferInstance)
  haveI : IsProper Fs.hom := aN.w ▸ (inferInstance : IsProper (aN.left ≫ (s2b_normalizationOver Xbase η).hom))
  haveI : T2Space (ComplexPoint Fs) :=
    (ComplexPoint.isClosedEmbedding_map_of_closedImmersion aN).isEmbedding.t2Space
  have hk₁u : k₁.left ≫ uM.left = jO.left := congrArg (fun k => k.left) hjk₁
  have hAb : JA.left ≫ JN.left ≫ βN.left =
      Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) ≫ jO.left := by
    change JA.left ≫ JN.left ≫ η.fromNormalization = _
    simpa only [Category.assoc, hk₁u] using hJAbase
  have hBb : JB.left ≫ JN.left ≫ βN.left =
      Spec.map (CommRingCat.ofHom (algebraMap A₂ (integralClosure A₂ L))) ≫ jB.left := hJBbase
  have hAr : Set.range (JA.left ≫ JN.left) = βN.left ⁻¹' Set.range jO.left := by
    change Set.range (JA.left ≫ JN.left) = η.fromNormalization ⁻¹' Set.range jO.left
    simpa only [hk₁u] using hJArange
  have hBr : Set.range (JB.left ≫ JN.left) = βN.left ⁻¹' Set.range jB.left := hJBrange
  obtain ⟨Hc₁, Hc₂, hHc₁, hHc₂, hcovU, hratio₁, hratio₂⟩ := literal_reciprocal_slice_chart_data
    (R := R) (A := A) (A₂ := A₂) (L := L) βN p x JN lN hlN JA JB jO jB hAb hBb hAr hBr hcovN
    (regularPairCoefficientAlgHom u v) (regularPairCoefficientAlgHom v u) c hjOsq hjBsq φ hxφ
    vE vE₂ (RegularPairChart.ratio u v) (RegularPairChart.ratio v u)
    (by
      intro z y hy
      apply hRatio z y.left
      have hh := congrArg (fun k => k.left) hy
      change y.left ≫ jO.left = _ at hh
      rw [hjO, hjdef] at hh
      exact hh)
    (by
      intro z y hy
      apply hRatio₂ z y.left
      have hh := congrArg (fun k => k.left) hy
      change y.left ≫ (k₂.left ≫ uM.left) = _ at hh
      rw [hk₂M, huM] at hh
      exact hh)
  let U₁ : Set (ComplexPoint Fs) := {z | (Point.map As (Point.map Ps z)).left
    (IsLocalRing.closedPoint ℂ) ∈ Set.range jO.left}
  let U₂ : Set (ComplexPoint Fs) := {z | (Point.map As (Point.map Ps z)).left
    (IsLocalRing.closedPoint ℂ) ∈ Set.range jB.left}
  let pA := fun z : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ =>
    (ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val
  let pB := fun z : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom v u) φ =>
    (ComplexPoint.affineSpecEquiv (integralClosure A₂ L)).symm z.val
  have hszero (z : integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom v u) φ) :
      z.val sB = 0 ↔ z.val (algebraMap A₂ (integralClosure A₂ L) (RegularPairChart.ratio v u)) = 0 :=
    integral_unit_power_zero_evaluation G qB sB hqBu (RegularPairChart.ratio v u)
      n hn (-Nat.gcdB n a') hsBpow z.val.toRingHom
  have hsE₂ (z) : ComplexPoint.affineSpecEquiv (integralClosure A₂ L) (pB z) sB = 0 ↔ (E₂ z).2 = 0 := by
    rw [Equiv.apply_symm_apply, hszero z, (hE₂ z).2.2, mul_eq_zero]
    simp only [hk₂, false_or]
    exact pow_eq_zero_iff (show m / Nat.gcd m α ≠ 0 from Nat.ne_of_gt hn)
  have hD₂zero (z) : (Point.map As z).left (IsLocalRing.closedPoint ℂ) ∈ D₂.support ↔
      vE₂ z = ((0 : ℂ) : OnePoint ℂ) := by
    simpa only [D₂, sup_comm] using (hEnds₂ z).1
  have hU₁ (z : ComplexPoint Fs) : z ∈ U₁ ↔ vE (Point.map Ps z) ≠ (∞ : OnePoint ℂ) := by
    exact (slice_chart_image_complement βN p x U.1 hxU jO.left D₂ hrange z).trans
      (not_congr (hEnds (Point.map Ps z)).2)
  have hoverlap₂ (z) : (Hc₂ z).val ∈ U₁ ↔ ComplexPoint.affineSpecEquiv (integralClosure A₂ L) (pB z) sB ≠ 0 := by
    have hc := slice_chart_image_complement βN p x U.1 hxU jO.left D₂ hrange (Hc₂ z).val
    have hvzero : vE₂ (Point.map Ps (Hc₂ z).val) = ((0 : ℂ) : OnePoint ℂ) ↔
        z.val (algebraMap A₂ (integralClosure A₂ L) (RegularPairChart.ratio v u)) = 0 := by
      constructor
      · intro hz
        exact OnePoint.coe_injective ((hratio₂ z).symm.trans hz)
      · intro hz
        exact (hratio₂ z).trans (congrArg (fun a : ℂ => (a : OnePoint ℂ)) hz)
    have hh := hc.trans ((not_congr (hD₂zero (Point.map Ps (Hc₂ z).val))).trans
      (not_congr hvzero))
    have hev : ComplexPoint.affineSpecEquiv (integralClosure A₂ L) (pB z) sB = z.val sB :=
      congrArg (fun f : integralClosure A₂ L →ₐ[ℂ] ℂ => f sB)
        ((ComplexPoint.affineSpecEquiv (integralClosure A₂ L)).apply_symm_apply z.val)
    refine hh.trans ((not_congr (hszero z)).symm.trans ?_)
    constructor
    · intro hz he
      exact hz (hev.symm.trans he)
    · intro hz he
      exact hz (hev.trans he)
  haveI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  have hmng : m = n * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left m α)).symm
  have hξ : IsPrimitiveRoot (ζ ^ n) g := IsPrimitiveRoot.pow hm hζ hmng
  have hξ₂ : IsPrimitiveRoot (ζ₂ ^ n) g := IsPrimitiveRoot.pow hm hζ₂ hmng
  let b₁ : ZMod g → ℂ := fun l => κ₁ * (ζ ^ n) ^ l.val
  let b₂ : ZMod g → ℂ := fun l => κ₂ * (ζ₂ ^ n) ^ l.val
  have rootinj (κ' ξ : ℂ) (hκ' : κ' ≠ 0) (hξ' : IsPrimitiveRoot ξ g) :
      Function.Injective (fun l : ZMod g => κ' * ξ ^ l.val) := by
    intro l k hh
    apply ZMod.val_injective
    exact hξ'.pow_inj (ZMod.val_lt l) (ZMod.val_lt k) (mul_left_cancel₀ hκ' hh)
  obtain ⟨er, her, _⟩ := binomial_root_relabelling g hg κ₁ (ζ ^ n) κ₂ (ζ₂ ^ n)
    hκ₁0 hκ₂0 hξ hξ₂ (hκ₁.trans hκ₂.symm)
  obtain ⟨EG, jc, hjc, hexjc, hjcE, hglobal, hfirst⟩ := actual_reciprocal_chart_sections
    (A := integralClosure A L) (B := integralClosure A₂ L)
    (TA := integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom u v) φ)
    (TB := integralCoefficientFibre (L := L) (regularPairCoefficientAlgHom v u) φ)
    (I := ZMod g) (K := ZMod g)
    Fs N (s2b_normalizationOver Xbase η) JN lN aN hlN JA JB Q T q₁ t₁ qB sB
    hQA hQB hTA hTB U₁ U₂ hcovU Hc₁.toEquiv Hc₂.toEquiv pA pB hHc₁ hHc₂
    E₁.toEquiv E₂.toEquiv b₁ b₂ (rootinj _ _ hκ₁0 hξ) (rootinj _ _ hκ₂0 hξ₂) er her
    (by intro z; rw [Equiv.apply_symm_apply]; exact (hE₁ z).1)
    (by intro z; rw [Equiv.apply_symm_apply]; exact (hE₁ z).2.1)
    (by intro z; rw [Equiv.apply_symm_apply, hqBeq]; exact (hE₂ z).1)
    hsE₂ hoverlap₂
  let δA : L ≃ₐ[A] L := δ.restrictScalars A
  let DC := integralCoefficientFibreDeck (regularPairCoefficientAlgHom u v) φ δA
  have hEigen := integral_binomial_eigenvalues (regularPairCoefficientAlgHom u v) φ δA
    (RegularPairChart.ratio u v) (wN : L) ζ hδw n a'
    (Nat.gcdA n a') (Nat.gcdB n a') q₁ t₁ hq₁ ht₁
  let cphase : ℂ := ζ ^ Nat.gcdB n a'
  have hcphase : cphase ≠ 0 := zpow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hm))
  have hcperiod : cphase ^ m = 1 := by
    change (ζ ^ Nat.gcdB n a') ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
  have hDC := binomial_labelled_deck_coordinates g hg κ₁ (ζ ^ n) cphase hκ₁0 hξ
    E₁.toEquiv (fun z => z.val q₁) (fun z => z.val t₁) DC
    (fun z => (hE₁ z).1) (fun z => (hE₁ z).2.1)
    (fun z => (hEigen z).1) (fun z => (hEigen z).2)
  haveI : Mono aN := Over.mono_of_mono_left aN
  haveI : IsOpenImmersion (JA ≫ JN).left := by
    change IsOpenImmersion (JA.left ≫ JN.left)
    infer_instance
  have hDeckChart : ∀ z, (Hc₁ (DC z)).val = Point.map (sliceDeck βN p x dN hdN) (Hc₁ z).val :=
    integral_chart_slice_deck (s2b_normalizationOver Xbase η) Xbase Bbase βN p x
      η.toNormalization (JA ≫ JN) hpA dN hdN δA hδN
      (regularPairCoefficientAlgHom u v) φ (fun z => (Hc₁ z).val) (fun z => (hHc₁ z).symm)
  have hfinite := classified_affine_deck U₁ Hc₁.toEquiv E₁.toEquiv EG
    (fun l z => Point.map (jc l) (lineCoordinate.symm z)) hfirst
    (by intro l z; rw [hjcE, lineCoordinate.apply_symm_apply])
    (Point.map (sliceDeck βN p x dN hdN)) DC cphase hDeckChart hDC
  have hdeck (l) := component_deck_extension Fs (sliceDeck βN p x dN hdN)
    (jc l) (jc (l + 1)) cphase hcphase (hfinite l)
  obtain ⟨vScaled, hprojection, hscalezero, hscaleInf⟩ := common_component_phase m α Fs
    (exceptionalSlice p x) Ps vE jc EG hjcE U₁ Hc₁.toEquiv E₁.toEquiv hfirst
    κ₁ ζ hκ₁0 (Nat.gcdB n a') hU₁ (by
      intro z
      exact (hratio₁ z).trans (congrArg (fun a : ℂ => (a : OnePoint ℂ)) (hE₁ z).2.2))
  let wC : integralClosure A L := ⟨(wN : L), wN.property⟩
  let z₀ := E₁.symm (0, (1 : ℂ))
  have hratio₀ : z₀.val (algebraMap A (integralClosure A L) (RegularPairChart.ratio u v)) ≠ 0 := by
    rw [(hE₁ z₀).2.2, E₁.apply_symm_apply]
    simpa only [one_pow, mul_one] using hk₁ (0 : ZMod g)
  have hwCeq : wC ^ m = algebraMap A (integralClosure A L)
      (RegularPairChart.coeff u v ε * RegularPairChart.ratio u v ^ α) := by
    apply Subtype.ext
    exact congrArg (fun z : normalizedChart F => (z : L)) heqN
  have hworder := integral_binomial_chart_order (regularPairCoefficientAlgHom u v) φ δA Fs
    (sliceDeck βN p x dN hdN) m α hm (sliceDeck_pow_eq_one βN p x dN hdN m hperiod)
    (fun z => (Hc₁ z).val) (fun z w h => Hc₁.injective (Subtype.ext h)) hDeckChart
    (RegularPairChart.coeff u v ε) (RegularPairChart.ratio u v)
    (ε.isUnit.map (RegularPairChart.coeff u v)) wC hwCeq ζ hζ hδw z₀ hratio₀
  dsimp only
  refine ⟨jc, vScaled, cphase, hcphase, hcperiod, hjc, hexjc, hdeck, hprojection, ?_, ?_, hworder⟩
  · intro z
    exact (hEnds z).1.trans (hscalezero z).symm
  · intro z
    exact (hEnds z).2.trans (hscaleInf z).symm

end AlgebraicGeometry.RamifiedNormalization.StageFour

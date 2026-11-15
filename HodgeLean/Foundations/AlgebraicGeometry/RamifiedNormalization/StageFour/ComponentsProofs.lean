import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EtaleCoefficientEquiv
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalEtaleEquation
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalRegularPairNormalizationChart
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineOpenFieldFactor
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalChartFractionField
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalChartOver
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RetainedBaseRatioSphere
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComparedChartComplement
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceChartComplement
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationSliceClassification
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProperDominantPoints
import HodgeLean.Foundations.Program.SchoenTowerN2b
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericFieldFactor
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.EquationProofs
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Basic
import Mathlib.RingTheory.RingHom.Etale

/-! # Retained cyclic-cover geometry, stage four
HC no distance; AV milestone no distance. -/

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

/-- Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15;
Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
Esnault–Viehweg, Lectures on Vanishing Theorems, section 3.
HC no distance; AV milestone no distance. -/
theorem retained_binomial_component_exhaustion_aux
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i))
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (horder : ∀ i, (End.of (d i)) ^ S.m = 1)
    (i : Fin r)
    (x : ComplexPoint (B i.castSucc))
    (hx₁ : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val, by omega⟩).support)
    (hx₂ : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).support)
    (havoid : ∀ t : Fin (2 * r), t.val ≠ 2 * i.val → t.val ≠ 2 * i.val + 1 →
      x.left (IsLocalRing.closedPoint ℂ) ∉ (D i.castSucc t).support) :
    let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let F := coveringSlice β (b i) x
    let E := exceptionalSlice (b i) x
    let P := sliceProjection β (b i) x
    let A := pullback.fst (b i) x
    ∃ (vE : ComplexPoint E ≃ₜ OnePoint ℂ)
      (eF : {z : ComplexPoint F //
        (Point.map A (Point.map P z)).left (IsLocalRing.closedPoint ℂ) ∉
          (D i.succ ⟨2 * i.val + 1, by omega⟩).support} ≃ₜ
            (ZMod (Nat.gcd S.m α) × ℂ))
      (k : ZMod (Nat.gcd S.m α) → ℂ),
      (∀ j, k j ≠ 0) ∧
      (∀ z, vE (Point.map P z.val) =
        ((k (eF z).1 * (eF z).2 ^ (S.m / Nat.gcd S.m α) : ℂ) : OnePoint ℂ)) ∧
      (∀ z : ComplexPoint E,
        ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
          (D i.succ ⟨2 * i.val, by omega⟩).support ↔ vE z = ((0 : ℂ) : OnePoint ℂ)) ∧
        ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
          (D i.succ ⟨2 * i.val + 1, by omega⟩).support ↔ vE z = (∞ : OnePoint ℂ))) := by
  haveI : ∀ j, IsDominant (η j) := s2v_l1b_original_tower_generic_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ B e₀ b
    (fun j => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
      D j.castSucc ⟨2 * j.val + 1, by omega⟩)
    hcartier hblowup η hη₀ hη
  obtain ⟨κ, hκ, hfield⟩ := s2v_l1b_kummer_cyclic_degree S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  obtain ⟨U, hηU, u, v, ε, t, hxU, hu, hv, hu0, hv0, ht, htgen, hteq,
    hvreg, hureg, hureg', hvreg', z, a₀, a₁, ha, hza, hzb, hzet⟩ :=
    regular_original_etale_equation S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  let φ₀ := ((η i.castSucc).appLE U.1 ⊤ hηU ≫
    (Scheme.ΓSpecIso W₀.left.functionField).hom).hom
  let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
  have hm : 0 < S.m := by have := S.three_le; omega
  have hα : α ≤ S.m := Nat.le_of_lt (hexp (σ ⟨2 * i.val, by omega⟩)).2
  have hηbase : η i.succ ≫ (b i).left = Spec.map (CommRingCat.ofHom φ₀) ≫ U.2.fromSpec := by
    rw [hη]
    exact (affine_open_field_factor (η i.castSucc) U hηU).symm
  obtain ⟨M, π, eM, j₁, j₂, hj₁, hj₂, heM, hπ₁, hπ₂, hcover, hoverlap,
    j, F, hjdef, hjopen, hFinj, hjbase, hFc, hFr, _, _, _, hFj, EN, wN,
    hEN, hENb, hwN, heqN, hgenN, zA, b₀, b₁, hb, hzb₀, hzb₁, hzA⟩ :=
    original_regular_pair_normalization_chart (B i.castSucc) (B i.succ) (b i)
      (D i.castSucc ⟨2 * i.val, by omega⟩) (D i.castSucc ⟨2 * i.val + 1, by omega⟩)
      (hcartier i) (hblowup i) U u v hu hv hvreg hureg hureg' hvreg'
      (η i.succ) φ₀ hηbase S.m α hm hα ε t hu0 hv0 ht htgen hteq
      (h + 1) z a₀ a₁ ha hza hzb hzet
  letI := s2e_step1_sectionAlgebra (B i.castSucc) U.1
  haveI : Nonempty U.1 := ⟨⟨x.left (IsLocalRing.closedPoint ℂ), hxU⟩⟩
  let K := (B i.castSucc).left.functionField
  let L := W₀.left.functionField
  letI : Algebra K L := κ.hom.toAlgebra
  haveI : Module.Finite K L := hfield.1
  haveI : IsGalois K L := hfield.2.1
  haveI : IsCyclic (L ≃ₐ[K] L) := hfield.2.2.1
  have hdegree : Module.finrank K L = S.m := hfield.2.2.2
  let R := Γ((B i.castSucc).left, U)
  let A := RegularPairChart.ring u v
  letI : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen (B i.castSucc).left U.1 U.2
  have hφ : κ.hom.comp (algebraMap R K) = φ₀ :=
    s2v_i2a_generic_field_coefficients (B i.castSucc).left (η i.castSucc) κ.hom hκ U.1 hηU
  have hvK : algebraMap R K v ≠ 0 := by
    intro hvK
    have h := DFunLike.congr_fun hφ v
    change κ.hom (algebraMap R K v) = φ₀ v at h
    rw [hvK, map_zero] at h
    exact hv0 h.symm
  obtain ⟨H, hHc, hHr, hHF, hfraction, hRtower, hAtower⟩ :=
    original_chart_fraction_field u v κ.hom F (hFc.trans hφ.symm) hFinj hvK
  letI : Algebra A K := H.toAlgebra
  letI : Algebra A L := F.toAlgebra
  haveI : IsFractionRing A K := hfraction
  haveI : IsScalarTower A K L := hAtower
  letI : Algebra ℂ L := (F.comp (algebraMap ℂ A)).toAlgebra
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr hFinj
  haveI : IsDomain A := IsDomain.of_faithfulSMul A L
  let eC := (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv
  let cE : MvPolynomial (Fin (h + 1)) ℂ →ₐ[ℂ] A := MvPolynomial.aeval zA
  have hcE : cE.toRingHom.Etale :=
    etale_coordinate_coefficient_equiv eC
      ((RegularPairChart.coeff u v).comp ((B i.castSucc).hom.appLE ⊤ U.1 le_top).hom) zA hzA
  have hcEX : cE (MvPolynomial.X b₀) = RegularPairChart.ratio u v := by
    exact (MvPolynomial.aeval_X zA b₀).trans hzb₀
  have hw0 : (wN : L) ≠ 0 := by rw [hwN]; exact div_ne_zero ht hv0
  have hwBin : (wN : L) ^ S.m = algebraMap A L (RegularPairChart.coeff u v ε) *
      (algebraMap A L (RegularPairChart.ratio u v)) ^ α := by
    have h := congrArg (fun q : normalizedChart F => (q : L)) heqN
    change (wN : L) ^ S.m = F (RegularPairChart.coeff u v ε * RegularPairChart.ratio u v ^ α) at h
    change (wN : L) ^ S.m = F (RegularPairChart.coeff u v ε) * F (RegularPairChart.ratio u v) ^ α
    simpa only [map_mul, map_pow] using h
  have hs : algebraMap A L (RegularPairChart.ratio u v) ≠ 0 := by
    change F (RegularPairChart.ratio u v) ≠ 0
    rw [hFr]
    exact div_ne_zero hu0 hv0
  obtain ⟨c, jO, φ, hc, hcopen, hjO, hjOsq, hxφ⟩ :=
    original_chart_over (B i.castSucc) (B i.succ) (b i) U u v j hjbase x hxU
  haveI : IsOpenImmersion jO.left := hjO.symm ▸ hjopen
  haveI : IsOpenImmersion c.left := hcopen
  have hFjO : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ jO.left = η i.succ := by
    rw [hjO]
    exact hFj
  haveI : IsOpenImmersion j₁ := hj₁
  haveI : IsOpenImmersion j₂ := hj₂
  obtain ⟨vE, hEnds, hRatio⟩ := retained_base_ratio_sphere (B i.castSucc) (B i.succ) (b i)
    U (D i.castSucc ⟨2 * i.val, by omega⟩) (D i.castSucc ⟨2 * i.val + 1, by omega⟩)
    u v hu hv hvreg' hureg x hxU hx₁ hx₂ M π eM heM j₁ j₂ hπ₁ hπ₂ hcover hoverlap
  let D₂ := s2c_strictTransform (b i).left (D i.castSucc ⟨2 * i.val + 1, by omega⟩)
    (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩)
  have hrange : Set.range jO.left = ((b i).left ⁻¹ᵁ U.1 : Set (B i.succ).left) \ D₂.support := by
    rw [hjO, hjdef]
    exact compared_chart_image_complement (b i).left U
      (D i.castSucc ⟨2 * i.val, by omega⟩) (D i.castSucc ⟨2 * i.val + 1, by omega⟩)
      u v hu hv hureg hvreg' M π eM heM j₁ j₂ hπ₁ hπ₂ hcover hoverlap
  obtain ⟨hproj, hfinite⟩ := s2v_n2b_selected_instances S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  haveI := hproj
  haveI := hfinite
  haveI : IsDominant (η i.succ).fromNormalization := by
    haveI : IsDominant ((η i.succ).toNormalization ≫ (η i.succ).fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      infer_instance
    exact IsDominant.of_comp (η i.succ).toNormalization (η i.succ).fromNormalization
  haveI : IsDominant (s2b_normalizationMap (B i.succ) (η i.succ)).left := by
    change IsDominant (η i.succ).fromNormalization
    infer_instance
  haveI : Mono c.left := inferInstance
  haveI : Mono c := Over.mono_of_mono_left c
  have hβ := proper_dominant_complex_points_surjective (s2b_normalizationMap (B i.succ) (η i.succ))
  obtain ⟨E, k, hk, hP⟩ := normalization_slice_binomial_homeomorph u v ε ε.isUnit
    (h + 1) cE hcE b₀ hcEX S.m α hm hdegree (wN : L) hw0 hwBin hgenN hs
    (B i.succ) (B i.castSucc) (η i.succ) (b i) x jO hFjO c hjOsq φ hxφ hβ D₂ vE
    (fun z => (hEnds z).2)
    (slice_chart_image_complement (s2b_normalizationMap (B i.succ) (η i.succ)) (b i) x U.1 hxU jO.left D₂ hrange)
    (by
      intro z y hy
      apply hRatio z y.left
      have h := congrArg (fun q => q.left) hy
      change y.left ≫ jO.left = _ at h
      rw [hjO, hjdef] at h
      exact h)
  dsimp only
  rw [htransform i ⟨2 * i.val, by omega⟩,
    htransform i ⟨2 * i.val + 1, by omega⟩]
  exact ⟨vE, E, k, hk, hP, hEnds⟩

example : (1 : ZMod (Nat.gcd 6 2)) ≠ 0 := by decide

end AlgebraicGeometry.RamifiedNormalization.StageFour

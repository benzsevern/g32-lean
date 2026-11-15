import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RetainedBaseEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialTransformSupport
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceBaseSupports
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ChartCoefficientSquares
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SchemeSliceBaseTopology

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The compared model retains both actual branch endpoints and the literal first-chart ratio in the same sphere coordinate. -/
theorem retained_base_ratio_sphere
    (B X : Over (Spec ↧ℂ)) [IsSeparated B.hom]
    [CompactSpace (ComplexPoint X)] [T2Space (ComplexPoint X)]
    (p : X ⟶ B) (U : B.left.affineOpens)
    (I J : B.left.IdealSheafData) (u v : Γ(B.left, U))
    (hu : I.ideal U = Ideal.span {u}) (hv : J.ideal U = Ideal.span {v})
    (hvreg : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (hureg : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (x : ComplexPoint B) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ U.1)
    (hxI : x.left (IsLocalRing.closedPoint ℂ) ∈ I.support)
    (hxJ : x.left (IsLocalRing.closedPoint ℂ) ∈ J.support)
    (M : Scheme) (π : M ⟶ Spec Γ(B.left, U))
    (e : (p.left ⁻¹ᵁ U.1).toScheme ≅ M)
    (he : e.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left)
    (j₁ : Spec ↧(RegularPairChart.ring u v) ⟶ M)
    (j₂ : Spec ↧(RegularPairChart.ring v u) ⟶ M)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hj₁ : j₁ ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)))
    (hj₂ : j₂ ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)))
    (hcover : ∀ y : M, (∃ a, j₁ a = y) ∨ ∃ a, j₂ a = y)
    (hintersection : ∀ y : Spec ↧(RegularPairChart.ring v u),
      (∃ a, j₁ a = j₂ y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal) :
    ∃ E : ComplexPoint (CategoryTheory.Limits.pullback p x) ≃ₜ OnePoint ℂ,
      (∀ z, ((Point.map (CategoryTheory.Limits.pullback.fst p x) z).left
          (IsLocalRing.closedPoint ℂ) ∈ (s2c_strictTransform p.left I (I ⊔ J)).support ↔
        E z = ((0 : ℂ) : OnePoint ℂ)) ∧
        ((Point.map (CategoryTheory.Limits.pullback.fst p x) z).left
          (IsLocalRing.closedPoint ℂ) ∈ (s2c_strictTransform p.left J (I ⊔ J)).support ↔
        E z = (∞ : OnePoint ℂ))) ∧
      ∀ (z : ComplexPoint (CategoryTheory.Limits.pullback p x))
        (q : Spec ↧ℂ ⟶ Spec ↧(RegularPairChart.ring u v)),
        q ≫ (j₁ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) =
          (Point.map (CategoryTheory.Limits.pullback.fst p x) z).left →
        E z = ((Spec.homEquivRingHom q (RegularPairChart.ratio u v) : ℂ) : OnePoint ℂ) := by
  letI := s2e_step1_sectionAlgebra B U.1
  let Xmodel := Over.mk (π ≫ ComplexPoint.affineSpecStructureMap Γ(B.left, U))
  let q : Xmodel ⟶ Over.mk (ComplexPoint.affineSpecStructureMap Γ(B.left, U)) :=
    Over.homMk π rfl
  obtain ⟨xR, i, H, hi, hxR, hH⟩ :=
    retained_model_point_fibre_homeomorph B X p U M π e he x hx
  let φ := ComplexPoint.affineSpecEquiv Γ(B.left, U) xR
  have hφ : (ComplexPoint.affineSpecEquiv Γ(B.left, U)).symm φ = xR :=
    Equiv.symm_apply_apply _ _
  have hu0 : φ u = 0 := retained_affine_generator_zero B U I x hxI u hu xR hxR
  have hv0 : φ v = 0 := retained_affine_generator_zero B U J x hxJ v hv xR hxR
  obtain ⟨k₁, hk₁, hpoint₁⟩ := chart_coefficient_square_over u v M π j₁ hj₁
  obtain ⟨k₂, hk₂, hpoint₂⟩ := chart_coefficient_square_over v u M π j₂ hj₂
  letI : IsOpenImmersion k₁.left := by rw [hk₁]; infer_instance
  letI : IsOpenImmersion k₂.left := by rw [hk₂]; infer_instance
  have hcover' : ∀ y : Xmodel.left, (∃ a, k₁.left a = y) ∨ ∃ a, k₂.left a = y := by
    intro y
    change (∃ a, k₁.left a = y) ∨ ∃ a, k₂.left a = y
    rw [hk₁, hk₂]
    exact hcover y
  have hintersection' : ∀ y : Spec ↧(RegularPairChart.ring v u),
      (∃ a, k₁.left a = k₂.left y) ↔ RegularPairChart.ratio v u ∉ y.asIdeal := by
    intro y
    rw [hk₁, hk₂]
    exact hintersection y
  let G := s2v_separatedPointFibreHomeomorph p x
  letI : CompactSpace (ComplexPoint (CategoryTheory.Limits.pullback p x)) :=
    s2v_schemeFibre_compact p x
  letI : CompactSpace {z : ComplexPoint X // Point.map p z = x} := G.compactSpace
  let Hφ : {z : ComplexPoint Xmodel // Point.map q z =
      (ComplexPoint.affineSpecEquiv Γ(B.left, U)).symm φ} ≃ₜ
      {z : ComplexPoint Xmodel // Point.map q z = xR} :=
    (Homeomorph.refl _).subtype (fun z => by rw [hφ]; rfl)
  let H' := Hφ.trans H
  letI : CompactSpace {z : ComplexPoint Xmodel // Point.map q z =
      (ComplexPoint.affineSpecEquiv Γ(B.left, U)).symm φ} := H'.symm.compactSpace
  letI : T2Space {z : ComplexPoint Xmodel // Point.map q z =
      (ComplexPoint.affineSpecEquiv Γ(B.left, U)).symm φ} := H'.isEmbedding.t2Space
  letI : IsOpenImmersion i.left := by rw [hi]; infer_instance
  have hiSq : i.left ≫ p.left = π ≫ U.2.fromSpec := by
    rw [hi, Category.assoc, ← he, e.inv_hom_id_assoc]
  have hsquare₁ : (k₁.left ≫ i.left) ≫ p.left =
      Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ U.2.fromSpec := by
    rw [Category.assoc, hiSq, ← Category.assoc, hk₁, hj₁]
  have hsquare₂ : (k₂.left ≫ i.left) ≫ p.left =
      Spec.map (CommRingCat.ofHom (RegularPairChart.coeff v u)) ≫ U.2.fromSpec := by
    rw [Category.assoc, hiSq, ← Category.assoc, hk₂, hj₂]
  obtain ⟨hIa, hJa⟩ := binomial_chart_transform_support p.left U u v I J hu hv
    hvreg (k₁.left ≫ i.left) hsquare₁
  obtain ⟨hJb, hIb⟩ := binomial_chart_transform_support p.left U v u J I hv hu
    hureg (k₂.left ≫ i.left) hsquare₂
  rw [sup_comm J I] at hJb hIb
  let D₁ : Set Xmodel.left := i.left ⁻¹'
    ((s2c_strictTransform p.left I (I ⊔ J)).support : Set X.left)
  let D₂ : Set Xmodel.left := i.left ⁻¹'
    ((s2c_strictTransform p.left J (I ⊔ J)).support : Set X.left)
  obtain ⟨E, hfinite, hinfty, hends⟩ := affine_slice_base_support_homeomorph u v φ hu0 hv0
    Xmodel q k₁ k₂ hpoint₁ hpoint₂ hcover' hintersection' D₁ D₂ hIa hIb hJa hJb
  refine ⟨G.trans (H'.symm.trans E), ?_, ?_⟩
  · intro z
    let y := H'.symm (G z)
    have hy : Point.map i y.val = (G z).val := by
      have hh : (H' y).val = Point.map i y.val := hH (Hφ y)
      rw [H'.apply_symm_apply] at hh
      exact hh.symm
    have hproj : (G z).val = Point.map (CategoryTheory.Limits.pullback.fst p x) z :=
      s2v_separatedPointFibreHomeomorph_projection p x z
    have hpoint := congrArg (fun a : ComplexPoint X => a.left (IsLocalRing.closedPoint ℂ))
      (hy.trans hproj)
    change i.left (y.val.left (IsLocalRing.closedPoint ℂ)) =
      (Point.map (CategoryTheory.Limits.pullback.fst p x) z).left
        (IsLocalRing.closedPoint ℂ) at hpoint
    have hend := hends y
    change (i.left (y.val.left (IsLocalRing.closedPoint ℂ)) ∈
        (s2c_strictTransform p.left I (I ⊔ J)).support ↔ E y = _) ∧
      (i.left (y.val.left (IsLocalRing.closedPoint ℂ)) ∈
        (s2c_strictTransform p.left J (I ⊔ J)).support ↔ E y = _) at hend
    rw [hpoint] at hend
    exact hend

  · intro z qpoint hqpoint
    have hqmap : qpoint ≫ (k₁.left ≫ i.left) =
        (Point.map (CategoryTheory.Limits.pullback.fst p x) z).left := by
      rw [hk₁, hi]
      exact hqpoint
    have hjiStruct : (k₁.left ≫ i.left) ≫ X.hom =
        ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v) := (k₁ ≫ i).w
    let qO : ComplexPoint (Over.mk
        (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v))) :=
      Over.homMk qpoint (by
        change qpoint ≫ ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v) =
          𝟙 (Spec ↧ℂ)
        rw [← hjiStruct, ← Category.assoc, hqmap]
        exact (Point.map (CategoryTheory.Limits.pullback.fst p x) z).w)
    have hqX : Point.map i (Point.map k₁ qO) = (G z).val := by
      apply Over.OverMorphism.ext
      change (qpoint ≫ k₁.left) ≫ i.left = (G z).val.left
      rw [Category.assoc, hqmap]
      exact congrArg (fun a : ComplexPoint X => a.left)
        (s2v_separatedPointFibreHomeomorph_projection p x z).symm
    let y := H'.symm (G z)
    have hy : (H' y).val = Point.map i y.val := hH (Hφ y)
    rw [H'.apply_symm_apply] at hy
    have hyY : y.val = Point.map k₁ qO :=
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points i).injective
        (hy.symm.trans hqX.symm)
    have hqbase : ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) qO =
        (ComplexPoint.affineSpecEquiv Γ(B.left, U)).symm φ := by
      rw [← hpoint₁ qO, ← hyY]
      exact y.property
    let Hchart := affineChartPointFibreHomeomorph u v φ hu0 hv0
    let r : ℂ := Hchart ⟨qO, hqbase⟩
    have hya : y = affineChartSliceMap u v φ hu0 hv0 Xmodel q k₁ hpoint₁ r := by
      apply Subtype.ext
      change y.val = Point.map k₁ (Hchart.symm (Hchart ⟨qO, hqbase⟩)).val
      rw [Hchart.symm_apply_apply]
      exact hyY
    change E y = ((Spec.homEquivRingHom qpoint (RegularPairChart.ratio u v) : ℂ) : OnePoint ℂ)
    rw [hya, hfinite]
    rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour

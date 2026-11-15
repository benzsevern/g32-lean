import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationReciprocalMaps
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.NormalizationOpenRestriction
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CoveringSliceOpenLift
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OpenChartRangeComposition

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Original reciprocal integral functions give simultaneous scheme maps on a model containing the actual covering slice, retaining both literal chart images. -/
theorem original_reciprocal_slice_maps
    {A B L : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Field L]
    (X Y M : Over (Spec ↧ℂ)) (b : X ⟶ Y) (x : ComplexPoint Y)
    (η : Spec ↧L ⟶ X.left) [IsDominant η] [QuasiCompact η] [QuasiSeparated η]
    [LocallyOfFiniteType (s2b_normalizationOver X η).hom]
    (U : Y.left.Opens) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ U)
    (u : M ⟶ X) [IsOpenImmersion u.left]
    (hu : Set.range u.left = (b.left ⁻¹ᵁ U : Set X.left))
    (jA : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ M)
    (jB : Over.mk (ComplexPoint.affineSpecStructureMap B) ⟶ M)
    [IsOpenImmersion jA.left] [IsOpenImmersion jB.left]
    (hcover : ∀ z : M.left, (∃ a, jA.left a = z) ∨ ∃ b, jB.left b = z)
    (f : A →+* L) (g : B →+* L)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ jA.left ≫ u.left = η)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ jB.left ≫ u.left = η)
    (q t : normalizedChart f) (q' s : normalizedChart g)
    (hqq : (q : L) = (q' : L)) (hts : (t : L) * (s : L) = 1) :
    letI := ((StageTwo.integralCoeff f).comp (algebraMap ℂ A)).toAlgebra
    letI := ((StageTwo.integralCoeff g).comp (algebraMap ℂ B)).toAlgebra
    ∃ (N : Over (Spec ↧ℂ))
      (J : N ⟶ s2b_normalizationOver X η)
      (l : coveringSlice (s2b_normalizationMap X η) b x ⟶ N)
      (JA : Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart f)) ⟶ N)
      (JB : Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart g)) ⟶ N)
      (Q : N ⟶ Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)))
      (T : N ⟶ projectiveLine),
      IsIntegral N.left ∧ LocallyOfFiniteType N.hom ∧
      IsOpenImmersion J.left ∧ IsOpenImmersion JA.left ∧ IsOpenImmersion JB.left ∧
      l ≫ J = pullback.fst (s2b_normalizationMap X η) (pullback.fst b x) ∧
      (JA.left ≫ J.left ≫ η.fromNormalization =
        Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff f)) ≫ jA.left ≫ u.left) ∧
      (JB.left ≫ J.left ≫ η.fromNormalization =
        Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff g)) ≫ jB.left ≫ u.left) ∧
      Set.range (JA.left ≫ J.left) = η.fromNormalization ⁻¹' Set.range (jA.left ≫ u.left) ∧
      Set.range (JB.left ≫ J.left) = η.fromNormalization ⁻¹' Set.range (jB.left ≫ u.left) ∧
      (∀ z : N.left, (∃ a, JA.left a = z) ∨ ∃ b, JB.left b = z) ∧
      JA ≫ Q = affineLineParameter q ∧ JB ≫ Q = affineLineParameter q' ∧
      JA ≫ T = projectiveLineChart 1 t ∧ JB ≫ T = projectiveLineChart 0 s ∧
      Spec.map (CommRingCat.ofHom (normalizedChart f).subtype) ≫ JA.left ≫ J.left = η.toNormalization ∧
      Spec.map (CommRingCat.ofHom (normalizedChart g).subtype) ≫ JB.left ≫ J.left = η.toNormalization := by
  letI := ((StageTwo.integralCoeff f).comp (algebraMap ℂ A)).toAlgebra
  letI := ((StageTwo.integralCoeff g).comp (algebraMap ℂ B)).toAlgebra
  let ηM := Spec.map (CommRingCat.ofHom f) ≫ jA.left
  have hηM : ηM ≫ u.left = η := by simpa only [ηM, Category.assoc] using hf
  haveI : IsDominant (ηM ≫ u.left) := hηM.symm ▸ inferInstance
  haveI : IsDominant ηM := IsDominant.of_comp_of_isOpenImmersion ηM u.left
  haveI : QuasiCompact ηM := inferInstance
  haveI : QuasiSeparated ηM := inferInstance
  obtain ⟨J, hJ, hb, hp, hr⟩ := normalization_open_restriction X M u η ηM hηM
  haveI : IsOpenImmersion J.left := hJ
  haveI : LocallyOfFiniteType (s2b_normalizationOver M ηM).hom := by
    rw [← J.w]
    infer_instance
  have hr' : Set.range J.left = η.fromNormalization ⁻¹' (b.left ⁻¹ᵁ U : Set X.left) := by
    rw [hr, hu]
  obtain ⟨l, hl, _⟩ := covering_slice_open_lift (s2b_normalizationMap X η) b x U hx J hr'
  have hgM : Spec.map (CommRingCat.ofHom g) ≫ jB.left = ηM := by
    apply (cancel_mono u.left).mp
    simpa only [Category.assoc] using hg.trans hηM.symm
  obtain ⟨JA, JB, Q, T, hJA, hJB, hbA, hbB, hrA, hrB, hcov, hQA, hQB, hTA, hTB, hpA, hpB⟩ :=
    normalization_reciprocal_maps M ηM jA jB hcover f g rfl hgM q t q' s hqq hts
  have hbase : J.left ≫ η.fromNormalization = ηM.fromNormalization ≫ u.left :=
    congrArg (fun z => z.left) hb
  have hsquare (z) : η.fromNormalization (J.left z) = u.left (ηM.fromNormalization z) :=
    congrArg (fun k => k z) hbase
  have hriA : Set.range (JA.left ≫ J.left) =
      η.fromNormalization ⁻¹' Set.range (jA.left ≫ u.left) :=
    open_chart_range_composition JA.left jA.left J.left u.left η.fromNormalization
      ηM.fromNormalization u.left.isOpenEmbedding.injective hsquare hr hrA
  have hriB : Set.range (JB.left ≫ J.left) =
      η.fromNormalization ⁻¹' Set.range (jB.left ≫ u.left) :=
    open_chart_range_composition JB.left jB.left J.left u.left η.fromNormalization
      ηM.fromNormalization u.left.isOpenEmbedding.injective hsquare hr hrB
  haveI : IsIntegral (s2b_normalizationOver M ηM).left := by
    change IsIntegral ηM.normalization
    infer_instance
  refine ⟨s2b_normalizationOver M ηM, J, l, JA, JB, Q, T, inferInstance, inferInstance,
    hJ, hJA, hJB, hl, ?_, ?_, hriA, hriB, hcov, hQA, hQB, hTA, hTB, ?_, ?_⟩
  · rw [hbase, ← Category.assoc, hbA, Category.assoc]
  · rw [hbase, ← Category.assoc, hbB, Category.assoc]
  · rw [← Category.assoc, hpA]
    exact hp
  · rw [← Category.assoc, hpB]
    exact hp

end AlgebraicGeometry.RamifiedNormalization.StageFour

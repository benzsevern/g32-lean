import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.OriginalReciprocalSliceMaps
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureComplexEquiv
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineLineParameterNaturality
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineChartNaturality

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original reciprocal scheme maps retain the canonical complex integral-closure spectra, their exact chart images and their original element parameters. -/
theorem literal_reciprocal_slice_maps
    {A B L : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Field L]
    [Algebra A L] [Algebra B L] [Algebra ℂ L] [IsScalarTower ℂ A L] [IsScalarTower ℂ B L]
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
    (hf : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ jA.left ≫ u.left = η)
    (hg : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ jB.left ≫ u.left = η)
    (q t : integralClosure A L) (q' s : integralClosure B L)
    (hqq : (q : L) = (q' : L)) (hts : (t : L) * (s : L) = 1) :
    ∃ (N : Over (Spec ↧ℂ))
      (J : N ⟶ s2b_normalizationOver X η)
      (l : coveringSlice (s2b_normalizationMap X η) b x ⟶ N)
      (JA : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶ N)
      (JB : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure B L)) ⟶ N)
      (Q : N ⟶ Over.mk (ComplexPoint.affineSpecStructureMap (Polynomial ℂ)))
      (T : N ⟶ projectiveLine),
      IsIntegral N.left ∧ LocallyOfFiniteType N.hom ∧
      IsOpenImmersion J.left ∧ IsOpenImmersion JA.left ∧ IsOpenImmersion JB.left ∧
      l ≫ J = pullback.fst (s2b_normalizationMap X η) (pullback.fst b x) ∧
      (JA.left ≫ J.left ≫ η.fromNormalization =
        Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) ≫ jA.left ≫ u.left) ∧
      (JB.left ≫ J.left ≫ η.fromNormalization =
        Spec.map (CommRingCat.ofHom (algebraMap B (integralClosure B L))) ≫ jB.left ≫ u.left) ∧
      Set.range (JA.left ≫ J.left) = η.fromNormalization ⁻¹' Set.range (jA.left ≫ u.left) ∧
      Set.range (JB.left ≫ J.left) = η.fromNormalization ⁻¹' Set.range (jB.left ≫ u.left) ∧
      (∀ z : N.left, (∃ a, JA.left a = z) ∨ ∃ b, JB.left b = z) ∧
      JA ≫ Q = affineLineParameter q ∧ JB ≫ Q = affineLineParameter q' ∧
      JA ≫ T = projectiveLineChart 1 t ∧ JB ≫ T = projectiveLineChart 0 s ∧
      Spec.map (CommRingCat.ofHom (integralClosure A L).subtype) ≫ JA.left ≫ J.left = η.toNormalization ∧
      Spec.map (CommRingCat.ofHom (integralClosure B L).subtype) ≫ JB.left ≫ J.left = η.toNormalization := by
  letI := ((StageTwo.integralCoeff (algebraMap A L)).comp (algebraMap ℂ A)).toAlgebra
  letI := ((StageTwo.integralCoeff (algebraMap B L)).comp (algebraMap ℂ B)).toAlgebra
  let eA := normalizedChartIntegralClosureComplexEquiv (A := A) (L := L)
  let eB := normalizedChartIntegralClosureComplexEquiv (A := B) (L := L)
  let XA := (letI := ((StageTwo.integralCoeff (algebraMap A L)).comp (algebraMap ℂ A)).toAlgebra
    Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart (algebraMap A L))))
  let XB := (letI := ((StageTwo.integralCoeff (algebraMap B L)).comp (algebraMap ℂ B)).toAlgebra
    Over.mk (ComplexPoint.affineSpecStructureMap (normalizedChart (algebraMap B L))))
  let eAO : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ≅ XA :=
    Over.isoMk (Scheme.Spec.mapIso eA.toRingEquiv.toCommRingCatIso.op)
      (ComplexPoint.specMap_comp_affineSpecStructureMap eA.toAlgHom)
  let eBO : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure B L)) ≅ XB :=
    Over.isoMk (Scheme.Spec.mapIso eB.toRingEquiv.toCommRingCatIso.op)
      (ComplexPoint.specMap_comp_affineSpecStructureMap eB.toAlgHom)
  have hemapA : eAO.hom.left = Spec.map (CommRingCat.ofHom eA.toAlgHom.toRingHom) := by
    change Spec.map eA.toRingEquiv.toCommRingCatIso.hom = _
    congr 1
  have hemapB : eBO.hom.left = Spec.map (CommRingCat.ofHom eB.toAlgHom.toRingHom) := by
    change Spec.map eB.toRingEquiv.toCommRingCatIso.hom = _
    congr 1
  obtain ⟨N, J, l, JA₀, JB₀, Q, T, hN, hNl, hJ, hJA₀, hJB₀, hl,
    hbA, hbB, hrA, hrB, hcov, hQA, hQB, hTA, hTB, hpA, hpB⟩ :=
    original_reciprocal_slice_maps X Y M b x η U hx u hu jA jB hcover
      (algebraMap A L) (algebraMap B L) hf hg
      (eA.symm q) (eA.symm t) (eB.symm q') (eB.symm s) hqq hts
  let JA := eAO.hom ≫ JA₀
  let JB := eBO.hom ≫ JB₀
  have hsurA : Function.Surjective eAO.hom.left := by
    intro z
    exact ⟨eAO.inv.left z, congrArg (fun k => k.left z) eAO.inv_hom_id⟩
  have hsurB : Function.Surjective eBO.hom.left := by
    intro z
    exact ⟨eBO.inv.left z, congrArg (fun k => k.left z) eBO.inv_hom_id⟩
  have hrcA : Set.range JA.left = Set.range JA₀.left := by
    change Set.range (JA₀.left ∘ eAO.hom.left) = _
    rw [Set.range_comp, hsurA.range_eq, Set.image_univ]
  have hrcB : Set.range JB.left = Set.range JB₀.left := by
    change Set.range (JB₀.left ∘ eBO.hom.left) = _
    rw [Set.range_comp, hsurB.range_eq, Set.image_univ]
  haveI : IsOpenImmersion JA₀.left := hJA₀
  haveI : IsOpenImmersion JB₀.left := hJB₀
  refine ⟨N, J, l, JA, JB, Q, T, hN, hNl, hJ, ?_, ?_, hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsOpenImmersion (eAO.hom.left ≫ JA₀.left)
    infer_instance
  · change IsOpenImmersion (eBO.hom.left ≫ JB₀.left)
    infer_instance
  · change (Spec.map (CommRingCat.ofHom eA.toRingHom) ≫ JA₀.left) ≫ J.left ≫ η.fromNormalization = _
    rw [Category.assoc, hbA, ← Category.assoc, ← Spec.map_comp]
    rfl
  · change (Spec.map (CommRingCat.ofHom eB.toRingHom) ≫ JB₀.left) ≫ J.left ≫ η.fromNormalization = _
    rw [Category.assoc, hbB, ← Category.assoc, ← Spec.map_comp]
    rfl
  · change Set.range ((JA₀.left ≫ J.left) ∘ eAO.hom.left) = _
    rw [Set.range_comp, hsurA.range_eq, Set.image_univ]
    exact hrA
  · change Set.range ((JB₀.left ≫ J.left) ∘ eBO.hom.left) = _
    rw [Set.range_comp, hsurB.range_eq, Set.image_univ]
    exact hrB
  · intro z
    rcases hcov z with ha | hb
    · left
      change z ∈ Set.range JA.left
      rw [hrcA]
      exact ha
    · right
      change z ∈ Set.range JB.left
      rw [hrcB]
      exact hb
  · change (eAO.hom ≫ JA₀) ≫ Q = _
    rw [Category.assoc, hQA]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [hemapA]
    simpa only [Over.comp_left, Over.homMk_left, AlgEquiv.toAlgHom_apply, eA.apply_symm_apply] using
      congrArg (fun k => k.left) (affineLineParameter_naturality eA.toAlgHom (eA.symm q))
  · change (eBO.hom ≫ JB₀) ≫ Q = _
    rw [Category.assoc, hQB]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [hemapB]
    simpa only [Over.comp_left, Over.homMk_left, AlgEquiv.toAlgHom_apply, eB.apply_symm_apply] using
      congrArg (fun k => k.left) (affineLineParameter_naturality eB.toAlgHom (eB.symm q'))
  · change (eAO.hom ≫ JA₀) ≫ T = _
    rw [Category.assoc, hTA]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [hemapA]
    simpa only [Over.comp_left, Over.homMk_left, AlgEquiv.toAlgHom_apply, eA.apply_symm_apply] using
      congrArg (fun k => k.left) (projectiveLineChart_naturality eA.toAlgHom 1 (eA.symm t))
  · change (eBO.hom ≫ JB₀) ≫ T = _
    rw [Category.assoc, hTB]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [hemapB]
    simpa only [Over.comp_left, Over.homMk_left, AlgEquiv.toAlgHom_apply, eB.apply_symm_apply] using
      congrArg (fun k => k.left) (projectiveLineChart_naturality eB.toAlgHom 0 (eB.symm s))
  · have he : Spec.map (CommRingCat.ofHom (integralClosure A L).subtype) ≫ eAO.hom.left =
        Spec.map (CommRingCat.ofHom (normalizedChart (algebraMap A L)).subtype) := by
      rw [hemapA, ← Spec.map_comp]
      rfl
    change Spec.map (CommRingCat.ofHom (integralClosure A L).subtype) ≫
      (eAO.hom.left ≫ JA₀.left) ≫ J.left = _
    calc
      _ = (Spec.map (CommRingCat.ofHom (integralClosure A L).subtype) ≫ eAO.hom.left) ≫
          JA₀.left ≫ J.left := by simp only [Category.assoc]
      _ = _ := by rw [he]; exact hpA
  · have he : Spec.map (CommRingCat.ofHom (integralClosure B L).subtype) ≫ eBO.hom.left =
        Spec.map (CommRingCat.ofHom (normalizedChart (algebraMap B L)).subtype) := by
      rw [hemapB, ← Spec.map_comp]
      rfl
    change Spec.map (CommRingCat.ofHom (integralClosure B L).subtype) ≫
      (eBO.hom.left ≫ JB₀.left) ≫ J.left = _
    calc
      _ = (Spec.map (CommRingCat.ofHom (integralClosure B L).subtype) ≫ eBO.hom.left) ≫
          JB₀.left ≫ J.left := by simp only [Category.assoc]
      _ = _ := by rw [he]; exact hpB

end AlgebraicGeometry.RamifiedNormalization.StageFour

import HodgeLean.Foundations.Analytic.AnalytificationDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Analytic

private lemma AnalytificationDbl_isOpenImmersion_eqToHom_comp
    {X Y Z : Scheme} (e : X = Y) (f : Y ⟶ Z) [IsOpenImmersion f] :
    IsOpenImmersion (eqToHom e ≫ f) := by
  letI : IsOpenImmersion (eqToHom e) := IsOpenImmersion.of_isIso _
  apply IsOpenImmersion.comp

private abbrev AnalytificationDblLine : Scheme := (f4_affineSpace 1).left

private abbrev AnalytificationDblPunctured : AnalytificationDblLine.Opens :=
  AnalytificationDblLine.basicOpen (AffineSpace.coord (Spec ↧ℂ) 0)

def AnalytificationDblGlueData' : CategoryTheory.GlueData' Scheme where
  J := Bool
  U _ := AnalytificationDblLine
  V _ _ _ := AnalytificationDblPunctured.toScheme
  f _ _ _ := AnalytificationDblPunctured.ι
  t _ _ _ := 𝟙 _
  t_inv _ _ _ := by simp
  t' i j k hij hik hjk := False.elim (by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all)
  t_fac i j k hij hik hjk := False.elim (by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all)
  cocycle i j k hij hik hjk := False.elim (by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all)

def AnalytificationDblGlueData : Scheme.GlueData.{0} :=
  { toGlueData := CategoryTheory.GlueData.ofGlueData' AnalytificationDblGlueData'
    f_open := by
      intro i j
      classical
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs
      · infer_instance
      · dsimp [AnalytificationDblGlueData']
        apply AnalytificationDbl_isOpenImmersion_eqToHom_comp }

abbrev AnalytificationDblScheme : Scheme := AnalytificationDblGlueData.glued

def AnalytificationDblToSpec : AnalytificationDblScheme ⟶ Spec ↧ℂ :=
  Multicoequalizer.desc AnalytificationDblGlueData.toGlueData.diagram _
    (fun _ ↦ (f4_affineSpace 1).hom) (by
      rintro ⟨i, j⟩
      rw [CategoryTheory.GlueData.diagram_fst, CategoryTheory.GlueData.diagram_snd]
      change Bool at i j
      cases i <;> cases j <;>
        simp [AnalytificationDblGlueData, AnalytificationDblGlueData',
          CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f'])

abbrev AnalytificationDbl : Over (Spec ↧ℂ) := Over.mk AnalytificationDblToSpec

lemma AnalytificationDbl_ι_toSpec (i : Bool) :
    AnalytificationDblGlueData.ι i ≫ AnalytificationDblToSpec = (f4_affineSpace 1).hom := by
  apply Multicoequalizer.π_desc

def AnalytificationDblChart (i : Bool) : f4_affineSpace 1 ⟶ AnalytificationDbl :=
  Over.homMk (AnalytificationDblGlueData.ι i) (AnalytificationDbl_ι_toSpec i)

def AnalytificationDblPoint (i : Bool) (z : ℂ) : ComplexPoint AnalytificationDbl :=
  Point.map (AnalytificationDblChart i)
    ((ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ z))

lemma AnalytificationDblPoint_mem_punctured {z : ℂ} (hz : z ≠ 0) :
    (ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ z) ∈
      Point.overOpen AnalytificationDblPunctured := by
  change (ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ z) ∈
    Point.overOpen (AnalytificationDblLine.basicOpen (AffineSpace.coord (Spec ↧ℂ) 0))
  apply (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
    (X := f4_affineSpace 1) (U := ⊤) (AffineSpace.coord (Spec ↧ℂ) 0) _ (by trivial)).2
  rw [ComplexPoint.evaluate_top_eq_appTop]
  change (ComplexPoint.affineSpaceEquiv (Fin 1)
    ((ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ z))) 0 ≠ 0
  rw [Equiv.apply_symm_apply]
  exact hz

lemma AnalytificationDblPoint_eq_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    AnalytificationDblPoint false z = AnalytificationDblPoint true z := by
  let p := (ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ z)
  let q := ComplexPoint.asOpenPoint (f4_affineSpace 1) AnalytificationDblPunctured p
    (AnalytificationDblPoint_mem_punctured hz)
  apply Over.OverMorphism.ext
  change p.left ≫ AnalytificationDblGlueData.ι false =
    p.left ≫ AnalytificationDblGlueData.ι true
  have h : AnalytificationDblPunctured.ι ≫ AnalytificationDblGlueData.ι false =
      AnalytificationDblPunctured.ι ≫ AnalytificationDblGlueData.ι true := by
    convert (AnalytificationDblGlueData.glue_condition false true).symm using 1 <;>
      simp [AnalytificationDblGlueData, AnalytificationDblGlueData',
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
  calc
    p.left ≫ AnalytificationDblGlueData.ι false =
        (q.left ≫ AnalytificationDblPunctured.ι) ≫
          AnalytificationDblGlueData.ι false := by
      exact congrArg (fun f ↦ f ≫ AnalytificationDblGlueData.ι false)
        (ComplexPoint.liftToOpen_fac (f4_affineSpace 1) AnalytificationDblPunctured p
          (AnalytificationDblPoint_mem_punctured hz)).symm
    _ = (q.left ≫ AnalytificationDblPunctured.ι) ≫
          AnalytificationDblGlueData.ι true := by
      exact (Category.assoc _ _ _).trans ((congrArg (fun f ↦ q.left ≫ f) h).trans
        (Category.assoc _ _ _).symm)
    _ = p.left ≫ AnalytificationDblGlueData.ι true := by
      exact congrArg (fun f ↦ f ≫ AnalytificationDblGlueData.ι true)
        (ComplexPoint.liftToOpen_fac (f4_affineSpace 1) AnalytificationDblPunctured p
          (AnalytificationDblPoint_mem_punctured hz))

lemma AnalytificationDblPoint_zero_ne :
    AnalytificationDblPoint false 0 ≠ AnalytificationDblPoint true 0 := by
  intro h
  have hu := congrArg Point.underlying h
  change AnalytificationDblGlueData.ι false
      ((ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ 0)).underlying =
    AnalytificationDblGlueData.ι true
      ((ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ 0)).underlying at hu
  obtain ⟨x, hx, -⟩ := (AnalytificationDblGlueData.ι_eq_iff _ _ _ _).1 hu
  simp only [AnalytificationDblGlueData, AnalytificationDblGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', Bool.false_eq_true,
    dite_false, eqToHom_refl, Category.id_comp] at x hx
  have hp : (ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ 0) ∈
      Point.overOpen AnalytificationDblPunctured := by
    change ((ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ 0)).underlying ∈
      AnalytificationDblPunctured
    rw [← hx]
    change AnalytificationDblPunctured.ι _ ∈ AnalytificationDblPunctured
    exact Subtype.property _
  change _ ∈ Point.overOpen (AnalytificationDblLine.basicOpen
    (AffineSpace.coord (Spec ↧ℂ) 0)) at hp
  have hp' := (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
    (X := f4_affineSpace 1) (U := ⊤) (AffineSpace.coord (Spec ↧ℂ) 0) _ (by trivial)).1 hp
  rw [ComplexPoint.evaluate_top_eq_appTop] at hp'
  change (ComplexPoint.affineSpaceEquiv (Fin 1)
    ((ComplexPoint.affineSpaceEquiv (Fin 1)).symm (fun _ ↦ 0))) 0 ≠ 0 at hp'
  rw [Equiv.apply_symm_apply] at hp'
  exact hp' rfl

lemma AnalytificationDblPoint_continuous (i : Bool) :
    Continuous (AnalytificationDblPoint i) := by
  apply (Point.continuous_map (AnalytificationDblChart i)).comp
  apply (ComplexPoint.affineSpaceHomeomorph (Fin 1)).symm.continuous.comp
  exact continuous_pi fun _ ↦ continuous_id

lemma AnalytificationDbl_not_t2Space : ¬ T2Space (ComplexPoint AnalytificationDbl) := by
  intro ht
  letI : T2Space (ComplexPoint AnalytificationDbl) := ht
  obtain ⟨U, V, hU, hV, h0U, h0V, hUV⟩ :=
    t2_separation AnalytificationDblPoint_zero_ne
  let A : Set ℂ := AnalytificationDblPoint false ⁻¹' U
  let B : Set ℂ := AnalytificationDblPoint true ⁻¹' V
  have hA : IsOpen A := hU.preimage (AnalytificationDblPoint_continuous false)
  have hB : IsOpen B := hV.preimage (AnalytificationDblPoint_continuous true)
  have h0A : 0 ∈ A := h0U
  have h0B : 0 ∈ B := h0V
  have hAB : IsOpen (A ∩ B) := hA.inter hB
  have hnAB : (A ∩ B).Nonempty := ⟨0, h0A, h0B⟩
  obtain ⟨z, hz0, hzA, hzB⟩ :=
    (dense_compl_singleton (0 : ℂ)).exists_mem_open hAB hnAB
  have hz : z ≠ 0 := by simpa using hz0
  have heq := AnalytificationDblPoint_eq_of_ne_zero hz
  exact hUV.le_bot ⟨hzA, heq ▸ hzB⟩

instance AnalytificationDbl_locallyOfFiniteType :
    LocallyOfFiniteType AnalytificationDbl.hom := by
  letI (i : AnalytificationDblGlueData.openCover.I₀) :
      IsAffine (AnalytificationDblGlueData.openCover.X i) := by
    exact f4_affineSpace_isAffine 1
  apply HasRingHomProperty.of_source_openCover AnalytificationDblGlueData.openCover
  intro i
  have hi : AnalytificationDblGlueData.openCover.f i ≫ AnalytificationDbl.hom =
      (f4_affineSpace 1).hom := AnalytificationDbl_ι_toSpec i
  rw [hi]
  exact HasRingHomProperty.appTop @LocallyOfFiniteType _
    (f4_affineSpace_locallyOfFiniteType 1)

instance AnalytificationDbl_compactSpace : CompactSpace AnalytificationDblScheme := by
  letI : Finite AnalytificationDblGlueData.openCover.I₀ := by
    change Finite Bool
    infer_instance
  letI (i : AnalytificationDblGlueData.openCover.I₀) :
      CompactSpace (AnalytificationDblGlueData.openCover.X i) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ (f4_affineSpace 1).hom
      (f4_affineSpace_quasiCompact 1) inferInstance
  exact AnalytificationDblGlueData.openCover.compactSpace

instance AnalytificationDbl_quasiCompact : QuasiCompact AnalytificationDbl.hom := by
  letI : CompactSpace AnalytificationDbl.left := AnalytificationDbl_compactSpace
  apply quasiCompact_of_compactSpace

end HodgeLean.Foundations.Analytic

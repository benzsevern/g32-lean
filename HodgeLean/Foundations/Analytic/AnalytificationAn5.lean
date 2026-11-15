import HodgeLean.Foundations.Analytic.AnalytificationAn4
import HodgeLean.Foundations.ComplexPointGroup
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

noncomputable section

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonoidalCategory

namespace HodgeLean.Foundations.Analytic

lemma AnalytificationAn5_isEmbedding_map_of_immersion
    {A B : Over (Spec ↧ℂ)} (i : A ⟶ B) [IsImmersion i.left] :
    IsEmbedding (Point.map i) := by
  let C : Over (Spec ↧ℂ) :=
    Over.mk (i.left.coborderRange.ι ≫ B.hom)
  let c : A ⟶ C := Over.homMk i.left.liftCoborder (by
    change i.left.liftCoborder ≫ i.left.coborderRange.ι ≫ B.hom = A.hom
    rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, Over.w i])
  let j : C ⟶ B := Over.homMk i.left.coborderRange.ι rfl
  letI : IsClosedImmersion c.left := by
    exact inferInstanceAs (IsClosedImmersion i.left.liftCoborder)
  have hc : IsEmbedding (Point.map c) :=
    ComplexPoint.isEmbedding_map_of_closedImmersion c
  have hj : IsEmbedding (Point.map j) :=
    (ComplexPoint.isOpenEmbedding_map_open B i.left.coborderRange).isEmbedding
  have hcomp : Point.map i = Point.map j ∘ Point.map c := by
    funext z
    apply Over.OverMorphism.ext
    change z.left ≫ i.left = (z.left ≫ i.left.liftCoborder) ≫
      i.left.coborderRange.ι
    rw [Category.assoc, Scheme.Hom.liftCoborder_ι]
  rw [hcomp]
  exact hj.comp hc

lemma AnalytificationAn5_cuspChart_toFun : f4_cuspChart.toFun =
    (fun z : ℂ ↦ ![z ^ 2, z ^ 3]) ∘
      (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)) ∘ affineSpaceHomeomorph (Fin 1) := by
  funext z
  ext i
  fin_cases i <;>
    simp only [f4_cuspChart, f4_RawChart.toFun, Matrix.cons_val_zero,
      Matrix.cons_val_one, Function.comp_apply, Homeomorph.piUnique_apply,
      affineSpaceHomeomorph, affineSpaceEquiv_apply] <;>
    rw [evaluate_top_eq_appTop] <;> simp

lemma AnalytificationAn5_cuspChart_eqns : f4_cuspChart.eqns =
    (fun w : Fin 2 → ℂ ↦ ![w 0 ^ 3 - w 1 ^ 2]) := by
  dsimp only [f4_cuspChart]
  funext w j
  fin_cases j
  simp [f4_RawChart.eqns]

lemma AnalytificationAn5_cuspChart_range :
    f4_cuspChart.toFun '' f4_cuspChart.dom = an_zeroLocus univ f4_cuspChart.eqns := by
  have heqns := AnalytificationAn5_cuspChart_eqns
  have hfun := AnalytificationAn5_cuspChart_toFun
  have hdom : f4_cuspChart.dom = univ := by
    ext z
    change (z.underlying ∈ (⊤ : (f4_affineSpace 1).left.Opens)) ↔ z ∈ univ
    simp
  dsimp only [f4_cuspChart] at heqns hfun hdom ⊢
  rw [heqns]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← AnalytificationAn4_cuspParam_range]
    rw [hfun]
    exact ⟨(Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)) (affineSpaceHomeomorph (Fin 1) z),
      mem_univ _, rfl⟩
  · rw [← AnalytificationAn4_cuspParam_range]
    rintro ⟨t, -, rfl⟩
    let z : ComplexPoint (f4_affineSpace 1) :=
      (affineSpaceHomeomorph (Fin 1)).symm
        ((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).symm t)
    refine ⟨z, ?_, ?_⟩
    · rw [hdom]
      exact mem_univ _
    · rw [hfun]
      simp [z]

lemma AnalytificationAn5_cuspChart_not_generates : ¬ f4_cuspChart.Generates := by
  intro h
  obtain ⟨p, hp⟩ := h (AffineSpace.coord (Spec ↧ℂ) 0)
  dsimp only [f4_cuspChart] at p hp
  have heq : ∀ z : ℂ, z = MvPolynomial.eval ![z ^ 2, z ^ 3] p := by
    intro z
    let x : ComplexPoint (f4_affineSpace 1) :=
      (affineSpaceHomeomorph (Fin 1)).symm (fun _ ↦ z)
    have hx : x ∈ f4_cuspChart.dom := by
      change x.underlying ∈ (⊤ : (f4_affineSpace 1).left.Opens)
      simp
    have := hp x hx
    have hcoord : Point.evaluate (⊤ : (f4_affineSpace 1).left.Opens)
        (AffineSpace.coord (Spec ↧ℂ) 0) x = z := by
      rw [evaluate_top_eq_appTop]
      change (affineSpaceEquiv (Fin 1) x) 0 = z
      exact congrFun ((affineSpaceEquiv (Fin 1)).apply_symm_apply (fun _ ↦ z)) 0
    have hchart : f4_cuspChart.toFun x = ![z ^ 2, z ^ 3] := by
      rw [AnalytificationAn5_cuspChart_toFun]
      simp [x]
      exact rfl
    change Point.evaluate (⊤ : (f4_affineSpace 1).left.Opens)
      (AffineSpace.coord (Spec ↧ℂ) 0) x = MvPolynomial.eval (f4_cuspChart.toFun x) p at this
    rw [hcoord, hchart] at this
    exact this
  have hd := AnalytificationAn4_cuspPolynomial_deriv_zero p
  have hid : HasDerivAt (fun z : ℂ ↦ z) 1 0 := hasDerivAt_id 0
  have : (1 : ℂ) = 0 :=
    (hid.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ (heq z).symm)).unique hd
  norm_num at this

def AnalytificationAn5_projOverIso (Y : Over (Spec ↧ℂ)) (d : ℕ) :
    f4_projOver Y d ≅ f4_projectiveSpace d ⊗ Y := by
  unfold f4_projOver f4_projectiveSpace ProjectiveSpace ProjectiveSpace.toBase
  refine Over.isoMk (pullback.congrHom (Subsingleton.elim
      (terminal.from Y.left) (Y.hom ≫ terminal.from (Spec ↧ℂ))) rfl ≪≫
    (pullbackRightPullbackFstIso (terminal.from (Spec ↧ℂ)) _ Y.hom).symm ≪≫
    pullbackSymmetry _ _) ?_
  change _ ≫ pullback.fst (pullback.fst (terminal.from (Spec ↧ℂ)) _) Y.hom ≫
    pullback.fst (terminal.from (Spec ↧ℂ)) _ = pullback.fst _ _ ≫ Y.hom
  simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc]
  conv_lhs =>
    rhs
    rw [← pullback.condition]
  simp

lemma AnalytificationAn5_projOver_homeomorph (Y : Over (Spec ↧ℂ)) (d : ℕ) :
    ∃ e : ComplexPoint (f4_projOver Y d) ≃ₜ
        ComplexPoint (f4_projectiveSpace d) × ComplexPoint Y,
      ∀ z, (e z).2 = Point.map (f4_projToBase Y d) z := by
  let E := AnalytificationAn5_projOverIso Y d
  let e := (Point.isoMapHomeomorph E).trans
    (HodgeLean.Foundations.complexPointProdHomeomorph _ _)
  refine ⟨e, fun z ↦ ?_⟩
  apply Over.OverMorphism.ext
  change z.left ≫ E.hom.left ≫ pullback.snd _ _ =
    z.left ≫ ProjectiveSpace.toBase (Fin (d + 1)) Y.left
  dsimp [E]
  simp [AnalytificationAn5_projOverIso, f4_projOver, f4_projectiveSpace,
    ProjectiveSpace.toBase, ProjectiveSpace]

end HodgeLean.Foundations.Analytic

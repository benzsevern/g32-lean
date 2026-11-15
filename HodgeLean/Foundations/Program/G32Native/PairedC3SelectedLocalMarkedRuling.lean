import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalIntersectionFibre
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedParameterMarkedIdeals
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveMarkedPoint
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveParameterSmooth
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedResidualBase
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRulingCharts
import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagram
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRatioAtlas
import HodgeLean.Foundations.Program.G32Native.PairedC3RatioOverlapComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRulingStepProperties

/-! # Three local assertions for the specified normalized ruling maps -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native


open CategoryTheory.Limits
open AlgebraicGeometry.RamifiedNormalization.StageFour


/-- The specified normalized ratio maps agree on overlaps of the actual
quotient cover, including overlaps of distinct base neighbourhoods.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.3, II.7.13 and III.10. -/
theorem pairedC3_selected_ruling_overlap_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    let A := pairedC3SelectedRulingCharts R P i hi
    let U := pairedC3ResidualQuotientCover.{0,0,0} M A.V A.covers
    ∀ j k, pullback.fst (U.f j) (U.f k) ≫ (A.map j).left =
      pullback.snd _ _ ≫ (A.map k).left := by
  classical
  dsimp only
  letI : IsIntegral (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  have hstep := pairedC3_selected_ruling_step_properties R P i
  letI : IsDominant (P.T.b i).left := hstep.1
  letI : QuasiCompact (P.T.b i).left := hstep.2
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i (by rfl)
  have hproper₀ : ((P.T.D i.castSucc ⟨2 * i.val, by omega⟩).comap
      (P.C.slices i.castSucc).left).support ≠ ⊤ := by
    rw [hp.1]
    exact paired_c3_residue_support_proper R.P.k (P.C.residue.indices i)
  have hproper₁ : ((P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
      (P.C.slices i.castSucc).left).support ≠ ⊤ := by
    rw [hp.2]
    exact paired_c3_residue_support_proper R.P.k (P.C.residue.indices i)
  intro j k
  exact PairedC3AffineRatioData.overlap_comparison hproper₀ hproper₁
    ((pairedC3SelectedRatioAtlas R P i hi).chart j)
    ((pairedC3SelectedRatioAtlas R P i hi).chart k)


/-- Each specified normalized ratio map is smooth into the projective line.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.3, II.7.13 and III.10. -/
theorem pairedC3_selected_ruling_chart_smooth_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    let A := pairedC3SelectedRulingCharts R P i hi
    let U := pairedC3ResidualQuotientCover.{0,0,0} M A.V A.covers
    ∀ j, Smooth (A.map j).left := by
  classical
  let C := pairedC3SelectedRulingParameters R P i hi
  let U := C.U
  let V := C.V
  let u := C.u
  let v := C.v
  let h₀ := C.h₀
  let h₁ := C.h₁
  let s := C.s
  let t := C.t
  let hdata := C.equations
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let D := K ⊔ (P.C.slices i.castSucc).left.ker
  let M := D.comap (P.T.b i).left
  have hbase : Smooth (D.subschemeι ≫ (P.T.B i.castSucc).hom) :=
    pairedC3_selected_residual_base_smooth R P.T P.W P.eFinal P.C i
  have huM x : u x ∈ D.ideal (U x) := by
    apply (show P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ≤ D from
      le_sup_of_le_left le_sup_left) (U x)
    rw [(hdata x).1]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hvM x : v x ∈ D.ideal (U x) := by
    apply (show P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩ ≤ D from
      le_sup_of_le_left le_sup_right) (U x)
    rw [(hdata x).2.1]
    exact Ideal.subset_span (Set.mem_singleton _)
  dsimp only
  intro j
  rcases j with ⟨x, k⟩
  refine Fin.cases ?_ (fun l => ?_) k
  · let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (U x) (V x 0) (h₀ x)
    let β := Units.map base.toMonoidHom (hdata x).2.2.2.2.1.unit
    change Smooth (pairedC3ResidualProjectiveMap (P.T.B i.succ) M (V x 0) 0
      ((β : Γ((P.T.B i.succ).left, V x 0) ⧸ M.ideal (V x 0)) *
        Ideal.Quotient.mk (M.ideal (V x 0)) (s x))).left
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (V x 0) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    dsimp only [pairedC3ResidualProjectiveMap, Over.homMk_left]
    apply pairedC3_projective_parameter_smooth
    exact pairedC3_supplied_scaled_smooth _ _ (P.T.b i) D (U x) (V x 0) (h₀ x)
      (u x) (v x) (huM x) (hvM x) (s x)
      (hdata x).2.2.2.2.2.2.2.1 (hdata x).2.2.2.2.2.2.2.2.1
      (hdata x).2.2.2.2.1.unit hbase
  · have hl : l = 0 := Subsingleton.elim _ _
    subst l
    let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (U x) (V x 1) (h₁ x)
    let β := Units.map base.toMonoidHom (hdata x).2.2.2.2.1.unit
    change Smooth (pairedC3ResidualProjectiveMap (P.T.B i.succ) M (V x 1) 1
      ((↑β⁻¹ : Γ((P.T.B i.succ).left, V x 1) ⧸ M.ideal (V x 1)) *
        Ideal.Quotient.mk (M.ideal (V x 1)) (t x))).left
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (V x 1) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    dsimp only [pairedC3ResidualProjectiveMap, Over.homMk_left]
    apply pairedC3_projective_parameter_smooth
    exact pairedC3_supplied_scaled_smooth _ _ (P.T.b i) D (U x) (V x 1) (h₁ x)
      (v x) (u x) (hvM x) (huM x) (t x)
      (hdata x).2.2.2.2.2.2.2.2.2.1 (hdata x).2.2.2.2.2.2.2.2.2.2
      (hdata x).2.2.2.2.1.unit⁻¹ hbase

/-- Each specified normalized ratio map has the actual slice intersection
as its fibre over the diagonal marked point.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.3, II.7.13 and III.10. -/
theorem pairedC3_selected_ruling_chart_marked_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    let A := pairedC3SelectedRulingCharts R P i hi
    let U := pairedC3ResidualQuotientCover.{0,0,0} M A.V A.covers
    let a := (residualIntersection (P.C.slices i.succ) M).hom
    let b := (residualIntersectionSecond (P.C.slices i.succ) M).left
    ∀ j, IsPullback (U.pullbackHom b j) ((U.pullback₁ b).f j ≫ a)
      (A.map j).left (projectiveLineChart 1 (1 : ℂ)).left := by
  classical
  let C := pairedC3SelectedRulingParameters R P i hi
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let D := K ⊔ (P.C.slices i.castSucc).left.ker
  let M := D.comap (P.T.b i).left
  dsimp only
  intro j
  rcases j with ⟨x, k⟩
  refine Fin.cases ?_ (fun l => ?_) k
  · let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (C.U x) (C.V x 0) (C.h₀ x)
    let β := Units.map base.toMonoidHom (C.equations x).2.2.2.2.1.unit
    let z := (↑β : Γ((P.T.B i.succ).left, C.V x 0) ⧸ M.ideal (C.V x 0)) *
      Ideal.Quotient.mk (M.ideal (C.V x 0)) (C.s x)
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (C.V x 0) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    have h := pairedC3_canonical_intersection_fibre (P.T.B i.succ)
      (P.C.slices i.succ).left.ker M (C.V x 0) 0 z
      (pairedC3_selected_parameter_marked_ideal_0 R P i C x)
    rw [pairedC3_projective_marked_chart_eq] at h
    exact h
  · have hl : l = 0 := Subsingleton.elim _ _
    subst l
    let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (C.U x) (C.V x 1) (C.h₁ x)
    let β := Units.map base.toMonoidHom (C.equations x).2.2.2.2.1.unit
    let z := (↑β⁻¹ : Γ((P.T.B i.succ).left, C.V x 1) ⧸ M.ideal (C.V x 1)) *
      Ideal.Quotient.mk (M.ideal (C.V x 1)) (C.t x)
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (C.V x 1) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    have h := pairedC3_canonical_intersection_fibre (P.T.B i.succ)
      (P.C.slices i.succ).left.ker M (C.V x 1) 1 z
      (pairedC3_selected_parameter_marked_ideal_1 R P i C x)
    rw [pairedC3_projective_marked_chart_eq] at h
    exact h


end HodgeLean.Foundations.Program.ResidueSelected

import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNOriginalReesMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSchemePairCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNNormalizedEquation
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartPresentation
import HodgeLean.Foundations.Program.G32Native.PairedC3IntegralSliceIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport

/-! # The actual ideal comparison near every point on the selected centre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
open AlgebraicGeometry.Conormal
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- Every point of the retained residue hyperplane has an ambient affine
neighborhood upstairs on which the original source-to-total ideal
comparison is invertible, using the supplied single-pair charts.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_route_n_centre_comparison_neighborhood
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r)
    (p : ((P.C.slices i.castSucc).left.ker.comap (P.T.b i).left).subscheme ⟶
      ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (sq : IsPullback p
      ((P.C.slices i.castSucc).left.ker.comap (P.T.b i).left).subschemeι
      (P.C.slices i.castSucc).left (P.T.b i).left)
    (x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ V : (P.T.B i.succ).left.affineOpens, (P.C.slices i.succ).left x ∈ V.1 ∧
      IsIso ((Scheme.Modules.pullback V.1.ι).map
        (idealPullbackMap (P.C.slices i.castSucc).left
          ((P.C.slices i.castSucc).left.ker.comap (P.T.b i).left).subschemeι
          (P.T.b i).left p sq.w)) := by
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI := P.C.sliceImmersion i.castSucc
  let i₀ := (P.C.slices i.castSucc).left
  let i₁ := (P.C.slices i.succ).left
  let σ := (P.T.b i).left
  let D := P.T.D i.castSucc ⟨2 * i.val, by omega⟩
  let E := P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  obtain ⟨U, u, v, hxU, hu, hv, V₁, V₂, h₁, h₂, e₁, e₂, hcover, he₁, he₂⟩ :=
    paired_c3_route_n_scheme_pair_charts R P i x hx
  letI : Nonempty (i₀ ⁻¹ᵁ U.1) := ⟨⟨x, hxU⟩⟩
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hD : (D.comap i₀).support ≠ ⊤ := by
    rw [hp.1]; exact paired_c3_residue_support_proper _ _
  have hE : (E.comap i₀).support ≠ ⊤ := by
    rw [hp.2]; exact paired_c3_residue_support_proper _ _
  obtain ⟨a, ha, _⟩ := paired_c3_affine_normalized_equation i₀ D E
    (hp.1.trans hp.2.symm) hE U u v hu hv
  obtain ⟨b, hb, _⟩ := paired_c3_affine_normalized_equation i₀ E D
    (hp.2.trans hp.1.symm) hD U v u hv hu
  have hrv : IsSMulRegular (Γ((P.T.B i.castSucc).left, U) ⧸ i₀.ker.ideal U) v :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
      (paired_c3_integral_slice_cancel i₀ E hE U v hv)
  have hru : IsSMulRegular (Γ((P.T.B i.castSucc).left, U) ⧸ i₀.ker.ideal U) u :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
      (paired_c3_integral_slice_cancel i₀ D hD U u hu)
  obtain ⟨_, hs₁, hk₁⟩ := paired_c3_pair_chart_presentation u v e₁
    (σ.appLE U.1 V₁.1 h₁).hom he₁
  obtain ⟨_, hs₂, hk₂⟩ := paired_c3_pair_chart_presentation v u e₂
    (σ.appLE U.1 V₂.1 h₂).hom he₂
  have hmem : i₁ x ∈ V₁.1 ⊔ V₂.1 := by
    rw [hcover]
    change σ (i₁ x) ∈ U.1
    rw [← Scheme.Hom.comp_apply, show i₁ ≫ σ = i₀ from congrArg Over.Hom.left (P.C.sliceComp i)]
    exact hxU
  rcases hmem with hm | hm
  · exact ⟨V₁, hm, paired_conormal_original_rees_ideal_map_isIso i₀ _ σ p sq
      U V₁ h₁ u v a (e₁ (ratio u v)) hs₁ hk₁ ha hrv⟩
  · exact ⟨V₂, hm, paired_conormal_original_rees_ideal_map_isIso i₀ _ σ p sq
      U V₂ h₂ v u b (e₂ (ratio v u)) hs₂ hk₂ hb hru⟩

#print axioms paired_c3_route_n_centre_comparison_neighborhood
end HodgeLean.Foundations.Program.G32Native

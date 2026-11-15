import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalSquare
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalTransform
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComponentNoncontainment
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNUnionComparisonMono
import HodgeLean.Foundations.Program.G32Native.PairedC3StageFrames

/-! # The retained-step monicity assembly from its natural total-transform map -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
open AlgebraicGeometry.Conormal HodgeLean.Adapters
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The actual total-transform union and the existing rank-k slice frames
reduce native retained-step monicity to invertibility of the natural
source-to-total ideal comparison along the next slice. The displayed
comparison is input data to this assembly.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8.17;
Fulton, Intersection Theory, Appendix B.6. -/
theorem paired_c3_route_n_comparison_mono_of_total_ideal
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
    (hcomp : IsIso ((Scheme.Modules.pullback (P.C.slices i.succ).left).map
      (idealPullbackMap (P.C.slices i.castSucc).left
        ((P.C.slices i.castSucc).left.ker.comap (P.T.b i).left).subschemeι
        (P.T.b i).left p sq.w))) :
    Mono (pairedC3StageComparison P i) := by
  let PP := ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)
  letI : IsIntegral PP := HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI := P.C.sliceImmersion i.castSucc
  letI := P.C.sliceImmersion i.succ
  letI := P.C.residue.curve
  let σ := (P.T.b i).left
  let i₀ := (P.C.slices i.castSucc).left
  let i₁ := (P.C.slices i.succ).left
  let I := i₀.ker.comap σ
  let t := I.subschemeι
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let L := K.comap σ ⊔ I
  obtain ⟨p₀, a, _, ha, _⟩ := paired_c3_route_n_total_square R P i
  have hc : i₁ ≫ σ = i₀ := congrArg Over.Hom.left (P.C.sliceComp i)
  have hap : a ≫ p = 𝟙 PP := by
    apply (cancel_mono i₀).mp
    rw [Category.assoc, sq.w, ← Category.assoc, ha, hc, Category.id_comp]
  let γ : g3_power R.Z (2 * R.P.k) ⟶ R.B₀ :=
    eqToHom (congrArg (g3_power R.Z) R.hselected.symm) ≫ R.γ
  letI : IsFinite γ.left := by dsimp only [γ, Over.comp_left]; infer_instance
  have hsurj : Function.Surjective (Point.map γ) := by
    obtain ⟨_, h, _⟩ := s2e_symmetric_quotient_reindex R.Z R.B₀
      (R.h + 1) (2 * R.P.k) R.hselected.symm R.γ R.hγinv R.hγsurj R.hγ
    exact h
  haveI := hcomp
  have hcc : (a ≫ p) ≫ i₀ = i₁ ≫ ((𝟙 _) ≫ σ) := by
    rw [hap, Category.id_comp, Category.id_comp, hc]
  have hm : Mono (comparisonMap i₀ i₁ ((𝟙 _) ≫ σ) (a ≫ p) hcc) := by
    apply paired_conormal_union_composite_mono i₀ t i₁ L.subschemeι σ p a sq.w ha hcc
      (by change I.subschemeι.ker = i₁.ker ⊓ L.subschemeι.ker
          rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
          exact paired_c3_route_n_total_transform R P i)
      (by simpa only [Scheme.IdealSheafData.range_subschemeι] using
        paired_c3_route_n_component_noncontainment R P i) R.P.k
    intro x
    obtain ⟨U₀, hx₀, ⟨e₀⟩⟩ := paired_retained_slice_conormal_frames R.Z R.B₀ R.P.k R.r
      γ hsurj P.T.B P.T.e₀ P.T.b P.T.D P.T.hcartier P.T.hblowup
      i.castSucc (P.C.slices i.castSucc) x
    obtain ⟨U₁, hx₁, ⟨e₁⟩⟩ := paired_retained_slice_conormal_frames R.Z R.B₀ R.P.k R.r
      γ hsurj P.T.B P.T.e₀ P.T.b P.T.D P.T.hcartier P.T.hblowup
      i.succ (P.C.slices i.succ) x
    let U := U₀ ⊓ U₁
    let ep := (Scheme.Modules.pullbackCongr hap).app (s2c_conormal i₀) ≪≫
      (Scheme.Modules.pullbackId PP).app (s2c_conormal i₀)
    let ef₀ := unionConormalFrameOnSmallerOpen _ U₀ U inf_le_left R.P.k e₀
    let ef₁ := unionConormalFrameOnSmallerOpen _ U₁ U inf_le_right R.P.k e₁
    exact ⟨U, ⟨hx₀, hx₁⟩, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso ep ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ ef₀⟩,
      ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ ef₁⟩⟩
  haveI : Mono (comparisonMap i₀ i₁ σ (𝟙 PP)
      ((Category.id_comp i₀).trans hc.symm)) := by
    apply (unionConormal_comparison_mono_iff i₀ i₁ σ (𝟙 PP)
      ((Category.id_comp i₀).trans hc.symm)).mpr
    have hq : (a ≫ p) ≫ i₀ = i₁ ≫ σ := by
      simpa only [Category.id_comp] using hcc
    have hmI : Mono ((Scheme.Modules.pullback i₁).map
        (idealPullbackMap i₀ i₁ σ (a ≫ p) hq)) := by
      exact (unionConormal_comparison_mono_iff i₀ i₁ σ (a ≫ p) hq).mp
        (unionConormal_comparison_mono_congr i₀ i₁ (Category.id_comp σ)
          (a ≫ p) hcc hq hm)
    rw [← idealPullbackMap_eq_of_ambient i₀ i₁ σ (a ≫ p) (𝟙 PP) hq
      ((Category.id_comp i₀).trans hc.symm)]
    exact hmI
  let e := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
  let f₀ := ((Scheme.Modules.pullbackId PP).app (s2c_conormal i₀)).inv ≫
    comparisonMap i₀ i₁ σ (𝟙 PP) ((Category.id_comp i₀).trans hc.symm)
  haveI : Mono f₀ := by dsimp only [f₀]; infer_instance
  letI := unionConormal_restrict_preservesFiniteLimits e.hom
  haveI : Mono ((Scheme.Modules.restrictFunctor e.hom).map f₀) :=
    preserves_mono_of_preservesLimit _ _
  exact unionConormal_mono_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback e.hom) f₀

#print axioms paired_c3_route_n_comparison_mono_of_total_ideal
end HodgeLean.Foundations.Program.G32Native

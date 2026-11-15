import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RatioOverlapComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRulingStepProperties

/-! # Normalized ruling maps at every retained stage -/
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
theorem pairedC3_route_n_ruling_overlap
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    let A := pairedC3RouteNRulingCharts R P i
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
    ((pairedC3RouteNRatioAtlas R P i).chart j)
    ((pairedC3RouteNRatioAtlas R P i).chart k)



#print axioms pairedC3_route_n_ruling_overlap
end HodgeLean.Foundations.Program.ResidueSelected

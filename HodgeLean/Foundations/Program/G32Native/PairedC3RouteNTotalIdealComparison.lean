import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNCentreComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNFlatOpenComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedOffCentre
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalSquare
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNOpenReesMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComparisonNearSlice

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
open AlgebraicGeometry.Conormal
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29


/-- The source-to-total natural ideal comparison is invertible along the
actual retained next slice.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8;
Fulton, Intersection Theory, Appendix B.6.
The two original Rees charts handle the residue hyperplane; the
off-centre isomorphism handles its complement. -/
theorem paired_c3_route_n_total_ideal_comparison_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let σ := (P.T.b i).left
    let i₀ := (P.C.slices i.castSucc).left
    let i₁ := (P.C.slices i.succ).left
    let I := i₀.ker.comap σ
    ∃ (p : I.subscheme ⟶ ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
      (sq : IsPullback p I.subschemeι i₀ σ),
      IsIso ((Scheme.Modules.pullback i₁).map
        (idealPullbackMap i₀ I.subschemeι σ p sq.w)) := by
  dsimp only
  letI := P.C.sliceImmersion i.castSucc
  obtain ⟨p, _, sq, _, _⟩ := paired_c3_route_n_total_square R P i
  refine ⟨p, sq, ?_⟩
  apply paired_module_pullback_isIso_near_image (P.C.slices i.succ).left
  intro x
  by_cases hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support
  · obtain ⟨V, hxV, hV⟩ := paired_c3_route_n_centre_comparison_neighborhood R P i p sq x hx
    exact ⟨V.1, hxV, hV⟩
  · let σ := (P.T.b i).left
    let i₀ := (P.C.slices i.castSucc).left
    let i₁ := (P.C.slices i.succ).left
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let U : (P.T.B i.castSucc).left.Opens :=
      ⟨(K.support : Set _)ᶜ, K.support.isClosed.isOpen_compl⟩
    obtain ⟨e, he, _⟩ := paired_c3_selected_off_centre_iso R P i
    haveI : IsIso (σ ∣_ U) := by
      rw [← he]
      infer_instance
    have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
    have hK : K.comap i₀ = s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) := by
      rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
    have hxU : i₀ x ∈ U := by
      change i₀ x ∉ (K.support : Set _)
      intro h
      apply hx
      rw [← hK, Scheme.IdealSheafData.support_comap]
      exact h
    have hyU : i₁ x ∈ σ ⁻¹ᵁ U := by
      change σ (i₁ x) ∈ U
      rw [← Scheme.Hom.comp_apply,
        show i₁ ≫ σ = i₀ from congrArg Over.Hom.left (P.C.sliceComp i)]
      exact hxU
    exact ⟨σ ⁻¹ᵁ U, hyU, paired_conormal_flat_open_ideal_map_isIso i₀ _ σ p sq U⟩

#print axioms paired_c3_route_n_total_ideal_comparison_aux
end HodgeLean.Foundations.Program.G32Native

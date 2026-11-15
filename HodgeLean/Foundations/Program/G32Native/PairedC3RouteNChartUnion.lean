import HodgeLean.Foundations.Program.G32Native.PairedC3IntegralChartUnion
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSchemePairCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartPresentation
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport

/-! # Actual total-transform identities on the two selected single-pair charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
open AlgebraicGeometry.RegularPairChart
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- At every retained residue point the two original Rees charts satisfy
the total-transform intersection identity with the actual next slice.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_route_n_chart_union
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r)
    (x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (V₁ V₂ : (P.T.B i.succ).left.affineOpens),
      (P.C.slices i.castSucc).left x ∈ U.1 ∧
      V₁.1 ⊔ V₂.1 = σ ⁻¹ᵁ U.1 ∧
      (∀ V ∈ ({V₁, V₂} : Set (P.T.B i.succ).left.affineOpens),
        I.ideal V = (P.C.slices i.succ).left.ker.ideal V ⊓
          ((K.comap σ).ideal V ⊔ I.ideal V)) := by
  dsimp only
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI := P.C.sliceImmersion i.castSucc
  obtain ⟨U, u, v, hxU, hu, hv, V₁, V₂, h₁, h₂, e₁, e₂, hcover, he₁, he₂⟩ :=
    paired_c3_route_n_scheme_pair_charts R P i x hx
  let s := e₁ (ratio u v)
  let t := e₂ (ratio v u)
  obtain ⟨hrel₁, hs₁, hk₁⟩ := paired_c3_pair_chart_presentation u v e₁ _ he₁
  obtain ⟨hrel₂, hs₂, hk₂⟩ := paired_c3_pair_chart_presentation v u e₂ _ he₂
  letI : Nonempty ((P.C.slices i.castSucc).left ⁻¹ᵁ U.1) :=
    ⟨⟨x, hxU⟩⟩
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hproper₁ : ((P.T.D i.castSucc ⟨2 * i.val, by omega⟩).comap
      (P.C.slices i.castSucc).left).support ≠ ⊤ := by
    rw [hp.1]
    exact paired_c3_residue_support_proper _ _
  have hproper₂ : ((P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
      (P.C.slices i.castSucc).left).support ≠ ⊤ := by
    rw [hp.2]
    exact paired_c3_residue_support_proper _ _
  have hfirst := paired_c3_integral_chart_union
    (P.C.slices i.castSucc).left (P.T.b i).left _ _ (hp.2.trans hp.1.symm)
    hproper₂ U V₁ h₁ v u s hv hu hrel₁ hs₁ hk₁
  have hsecond := paired_c3_integral_chart_union
    (P.C.slices i.castSucc).left (P.T.b i).left _ _ (hp.1.trans hp.2.symm)
    hproper₁ U V₂ h₂ u v t hu hv hrel₂ hs₂ hk₂
  rw [sup_comm (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩),
    ← P.C.sliceStrict i] at hfirst
  rw [← P.C.sliceStrict i] at hsecond
  refine ⟨U, V₁, V₂, hxU, hcover, ?_⟩
  intro V hV
  rcases Set.mem_insert_iff.mp hV with rfl | hV
  · exact hfirst
  · obtain rfl := Set.mem_singleton_iff.mp hV
    exact hsecond

#print axioms paired_c3_route_n_chart_union
end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.JointSelectedBase
import HodgeLean.Foundations.Program.G32Native.SelectedTowerAdjoint
import HodgeLean.Foundations.Program.G32Native.SelectedTowerPointClasses
import HodgeLean.Foundations.Program.G32Native.JointSelectedTraceProducer

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Retain the orientation classes that define the joint traces.
Source: g32n_selected_joint_traces; Schoen, Compositio Mathematica 65 (1988), pp. 15–18. -/
structure G32JointOrientedTrace
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀) extends G32JointTracePackage R T W eFinal f where
  o : LocalRationalOrientation (a3b4_an W.hom) (2*(2*R.P.k))
  o₀ : LocalRationalOrientation (a3b4_an R.W₀.hom) (2*(2*R.P.k))
  cW : Homology ℚ (a3b4_an W.hom) (2*(2*R.P.k))
  c₀ : Homology ℚ (a3b4_an R.W₀.hom) (2*(2*R.P.k))
  ho : ∀ x, localOrientation (a3b4_an W.hom) (2*(2*R.P.k)) cW x = o.generator x
  ho₀ : ∀ x, localOrientation (a3b4_an R.W₀.hom) (2*(2*R.P.k)) c₀ x = o₀.generator x
  hchart : ∀ (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (2*R.P.k) → ℂ)),
    (∀ j, (HodgeLean.Foundations.Analytic.f4_analytification W).IsHolFun (fun u : E.source => E u j)) →
    ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an W.hom) (2*(2*R.P.k)) cW x =
      localClassOfChart (2*R.P.k) E x hx
  hchart₀ : ∀ (E : OpenPartialHomeomorph (ComplexPoint R.W₀) (Fin (2*R.P.k) → ℂ)),
    (∀ j, (HodgeLean.Foundations.Analytic.f4_analytification R.W₀).IsHolFun (fun u : E.source => E u j)) →
    ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an R.W₀.hom) (2*(2*R.P.k)) c₀ x =
      localClassOfChart (2*R.P.k) E x hx
  trace_final : trr = orientationIntegral (a3b4_an W.hom) (2*(2*R.P.k)) cW
  trace_initial : tr₀ = orientationIntegral (a3b4_an R.W₀.hom) (2*(2*R.P.k)) c₀

/-- Construct traces, point normalizations and the adjoint from the same orientation witnesses. -/
theorem jointSelectedOrientedTrace_exists
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀)
    (hf : f 0 = T.eW.hom ∧ ∀ i : Fin R.r, f i.succ = T.w i ≫ f i.castSucc) :
    Nonempty (G32JointOrientedTrace R T W eFinal f) := by
  have hfu := s2e_towerTotalMap_unique _ T.eW.hom T.w f hf.1 hf.2
  have hequiv := s2e_towerTotalMap_equivariant _ T.eW.hom T.w T.d R.d₀ T.hdinit T.hdw (Fin.last R.r)
  have hsquare : (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ≫
      (eFinal.inv ≫ f (Fin.last R.r)) = (eFinal.inv ≫ f (Fin.last R.r)) ≫ R.d₀ := by
    simp only [Category.assoc, eFinal.hom_inv_id_assoc]
    rw [hfu, hequiv]
  have hjoint := g32n_selected_joint_traces S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder W eFinal (2 * R.P.k) R.hselected
  obtain ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ht, ht₀, hp, hpair₀⟩ := hjoint
  have hk : 0 < 2 * R.P.k := by
    have hh := R.hh
    have hselected := R.hselected
    omega
  have hperf := g32n_projective_middle_perfect W R.P.k hk o c hc
  have hperf₀ := g32n_projective_middle_perfect R.W₀ R.P.k hk o₀ c₀ hc₀
  let trr := orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (2 * R.P.k)) c
  let tr₀ := orientationIntegral (TopCat.of (ComplexPoint R.W₀)) (2 * (2 * R.P.k)) c₀
  let F := s2e_pullback ℚ (eFinal.inv ≫ f (Fin.last R.r)) (2 * R.P.k)
  let Br := s2e_middlePairing (TopCat.of (ComplexPoint W)) R.P.k trr
  let Bzero := s2e_middlePairing (TopCat.of (ComplexPoint R.W₀)) R.P.k tr₀
  obtain ⟨hpoint, hpoint₀⟩ := G32Native.selectedTower_native_point_classes W R.W₀ R.P.k
    o c o₀ c₀ hc hc₀ hchart hchart₀
  refine ⟨{
    o := o, o₀ := o₀, cW := c, c₀ := c₀, ho := hc, ho₀ := hc₀
    hchart := fun E hE x hx => hchart x E hx hE,
    hchart₀ := fun E hE x hx => hchart₀ x E hx hE, trace_final := rfl, trace_initial := rfl
    trr := trr, tr₀ := tr₀, h_T15_final := hperf, h_T15_initial := hperf₀
    h_T16_final_point := hpoint, h_T16_initial_point := hpoint₀
    G := s2e_pairingAdjoint Bzero hperf₀ Br F
    h_T18_adjoint := ?_, h_T18_retraction := ?_, h_T18_deck := ?_ }⟩
  · exact s2e_pairingAdjoint_pair Bzero hperf₀ Br F
  · apply s2e_pairingAdjoint_retraction
    intro u v
    change trr (HodgeLean.Foundations.Singular.cup _ _ (F u) (F v)) =
      tr₀ (HodgeLean.Foundations.Singular.cup _ _ u v)
    dsimp only [trr, tr₀, F, s2e_pullback]
    rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
    rw [hfu]
    exact htrace _
  · intro u
    have hm : S.m ≠ 0 := by have := S.three_le; omega
    haveI : IsIso (T.d 0) := (isUnit_iff_isIso _).mp (IsUnit.of_pow_eq_one (T.horder 0) hm)
    have he : R.d₀ = T.eW.inv ≫ T.d 0 ≫ T.eW.hom := by rw [T.hdinit, T.eW.inv_hom_id_assoc]
    haveI : IsIso R.d₀ := by rw [he]; infer_instance
    apply g32n_adjoint_deck Bzero hperf₀ Br F (s2e_pullback ℚ R.d₀ (2 * R.P.k))
      (s2e_pullback ℚ (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) (2 * R.P.k))
    · intro v
      refine ⟨s2e_pullback ℚ (inv R.d₀) (2 * R.P.k) v, ?_⟩
      have hmap := congrArg (fun L => L v) (s2e_quotient_pullback_comp R.d₀ (inv R.d₀) (2 * R.P.k))
      rw [IsIso.hom_inv_id, s2e_pullback_id] at hmap
      exact hmap.symm
    · exact hpair₀
    · exact hp
    · intro v
      have hmap := congrArg (fun g => s2e_pullback ℚ g (2 * R.P.k) v) hsquare
      simpa only [F, s2e_quotient_pullback_comp, LinearMap.comp_apply] using hmap



#print axioms jointSelectedOrientedTrace_exists
end HodgeLean.Foundations.Program

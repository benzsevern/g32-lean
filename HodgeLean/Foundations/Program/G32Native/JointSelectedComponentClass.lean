import HodgeLean.Foundations.Program.SchoenCycleC2NeighbourhoodHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ProjectiveCoheightHelpers
import HodgeLean.Foundations.Program.G32Native.JointSelectedComponent
import HodgeLean.Foundations.Program.G32Native.SelectedTowerSliceGeometry
import HodgeLean.Foundations.Program.G32Native.ComponentInstances
import HodgeLean.Foundations.Program.G32Native.NormalizedComponentClass

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.hQ

/-- Select the normalized class on the retained final component using its finite étale neighbourhood. -/
theorem jointSelectedComponentClass_exists
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (C : G32JointComponent R T W eFinal) :
    ∃! c : s2e_supportedClass W (s2e_componentCycle C.ι ℚ) R.P.k,
      a3b4_IsCycleClass W.hom (s2e_componentCycle C.ι ℚ) R.P.k c := by
  letI := C.h_T20_slice_immersion
  letI := C.h_T20_component_immersion
  obtain ⟨_, hQs, _⟩ := g32n_componentInstances R.P.k C.Q C.eQ
  letI := hQs
  obtain ⟨hfin, hft, hqc, hsep, hdim, U, hU, he⟩ :=
    G32Native.selected_tower_final_slice_neighbourhood S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder W eFinal
      R.P.k R.hselected C.ℓ C.h_T20_avoidance
  letI := hfin
  letI := hft
  letI := hqc
  letI := hsep
  let β := eFinal.inv ≫ s2b_normalizationMap (T.B (Fin.last R.r)) (T.η (Fin.last R.r))
  have hproj : C.ι ≫ β = C.eQ.hom ≫ C.ℓ := by
    simpa only [β, Category.assoc] using C.h_T20_square
  have hrange : Set.range (C.ι ≫ β).left ⊆ U := by
    rw [hproj]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨C.eQ.hom.left x, rfl⟩
  obtain ⟨V, hV, hsm⟩ := s2e_smooth_neighbourhood_of_etale C.ι β U hrange he
  have hcodim := s2e_projective_orbit_component_coheight R.P.k C.eQ C.ℓ
    C.ι (𝟙 W) β (Category.id_comp β) hproj U hU inferInstance he hdim 0
  have hcodim' : ∀ x ∈ (s2e_componentCycle C.ι ℚ).support,
      Order.coheight x = R.P.k := by
    simpa only [pow_zero, End.one_asHom, Category.comp_id] using hcodim
  exact g32w12_normalized_component_exists_unique C.ι R.P.k V hV hsm hcodim'

#print axioms jointSelectedComponentClass_exists
end HodgeLean.Foundations.Program

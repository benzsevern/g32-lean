import HodgeLean.Foundations.Program.SchoenCycleC2NeighbourhoodHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ProjectiveCoheightHelpers
import HodgeLean.Foundations.Program.G32Native.JointSelectedComponent
import HodgeLean.Foundations.Program.G32Native.SelectedTowerSliceGeometry
import HodgeLean.Foundations.Program.G32Native.ComponentInstances
import HodgeLean.Foundations.Program.G32Native.NormalizedComponentClass
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData
import HodgeLean.Foundations.Program.G32Native.PairedConormalProjectiveNumerical
import HodgeLean.Foundations.Program.G32Native.PairedResidualConormalSequence
import HodgeLean.Foundations.Program.G32Native.EtaleLocusConormal
import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.HyperplaneClass

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.hQ

/-- Residual presentation data on the retained slice supply its numerical functional.
The normal-field input is U1. No curve, quotient, slice or supported class is chosen here.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.6 and Sublemma 2.7;
Fulton, Intersection Theory, Corollary 6.3. -/
theorem jointSelected_numerical_of_residual
    (hNormalField : by_elab return (← Lean.getConstInfo
      ``HodgeLean.Foundations.BundleThom.joint_projective_selfRestriction_eq_bundleEuler).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S)
    (P : G32JointOrientedPositiveData R)
    (F : G32Native.PairedResidualPresentation
      (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)))
      (P.T.B (Fin.last R.r)) P.C.ℓ R.P.k
      ((Scheme.Modules.pushforward
        (s2c_subschemeι (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)))
          (s2e_hyperplaneIdeal R.P.k)).left).obj
        (SheafOfModules.unit (s2c_subscheme
          (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)))
          (s2e_hyperplaneIdeal R.P.k)).left.ringCatSheaf))) :
    ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint P.C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ,
      degree (s2e_normalEuler P.C.ι R.P.k P.c) ≠ 0 := by
  let T := P.T
  let W := P.W
  let eFinal := P.eFinal
  let C := P.C.toG32JointComponent
  letI : IsIntegral W.left := P.integralW
  letI : IsProjective W.hom := P.projectiveW
  letI := C.h_T20_slice_immersion
  letI := C.h_T20_component_immersion
  obtain ⟨_, hQs, hQp⟩ := g32n_componentInstances R.P.k C.Q C.eQ
  letI := hQs
  letI := hQp
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
  letI : SmoothOfRelativeDimension R.P.k C.Q.hom := by
    rw [← s2e_projective_model_dimension C.Q R.P.k C.eQ]
    infer_instance
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k) (T.B (Fin.last R.r)).hom := by
    have hb := (inferInstance : SmoothOfRelativeDimension
      (TopologicalSpace.dim (T.B (Fin.last R.r)).left) (T.B (Fin.last R.r)).hom)
    rw [hdim, two_mul] at hb
    exact hb
  let V := β.left ⁻¹ᵁ U
  let j := IsOpenImmersion.lift V.ι C.ι.left (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hrange ⟨x, rfl⟩)
  have hj : j ≫ V.ι = C.ι.left := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (j ≫ V.ι) := hj.symm ▸ C.h_T20_component_immersion
  letI : IsClosedImmersion j := IsClosedImmersion.of_comp j V.ι
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k)
      (U.ι ≫ (T.B (Fin.last R.r)).hom) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp
      0 (R.P.k + R.P.k) U.ι (T.B (Fin.last R.r)).hom
  letI := he
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k) (V.ι ≫ W.hom) := by
    have hsm := smoothOfRelativeDimension_comp 0 (R.P.k + R.P.k)
      (β.left ∣_ U) (U.ι ≫ (T.B (Fin.last R.r)).hom)
    simpa only [Nat.zero_add, morphismRestrict_ι_assoc, Over.w β] using hsm
  let PP : Over (Spec ↧ℂ) := Over.mk
    (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth R.P.k
  obtain ⟨f, g, hfg, hseq⟩ := G32Native.paired_residual_conormal_sequence C.ℓ R.P.k _ F
  obtain ⟨Eβ⟩ := G32Native.s2e_i1_etale_locus_component_conormalIso
    C.ℓ β U hU he C.eQ.hom C.ι hproj.symm
  obtain ⟨Ev⟩ := G32Native.i1_openConormalIso_aux C.ι V.ι j hj
  have hk : 0 < R.P.k := R.P.act.cyc_positive
  obtain ⟨hH, cH, hcH⟩ := G32Native.PrimitiveNonzero.hyperplane_class C.Q R.P.k hk C.eQ
  exact G32Native.paired_conormal_projective_numerical hNormalField
    C.ι R.P.k P.c P.hc V V.ι j hj hk C.eQ hH cH hcH
    (s2c_conormal C.ℓ.left) (Ev ≪≫ Eβ) f g hfg hseq

#print axioms jointSelected_numerical_of_residual
end ResidueSelected
end HodgeLean.Foundations.Program

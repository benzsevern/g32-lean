import HodgeLean.Foundations.Program.G32Native.JointSelectedOrientedTrace
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedSlicedComponent
import HodgeLean.Foundations.Program.G32Native.JointSelectedBaseProducer
import HodgeLean.Foundations.Program.G32Native.JointSelectedTraceProducer
import HodgeLean.Foundations.Program.G32Native.JointSelectedComponentClass
import HodgeLean.Foundations.Program.G32Native.SelectedTowerFinal
import HodgeLean.Foundations.Program.G32Native.SelectedTotalMaps

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointComponent.hQ

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Retain the orientations and coherent slice together on the selected tower.
Source: jointSelectedOrientedTrace_exists; ResidueSelected.jointSelectedSlicedComponent_exists. -/
structure G32JointOrientedPositiveData {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) where
  T : G32JointBase R
  W : Over (Spec ↧ℂ)
  [integralW : IsIntegral W.left]
  [projectiveW : IsProjective W.hom]
  eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W
  f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀
  hf : f 0 = T.eW.hom ∧ ∀ i : Fin R.r, f i.succ = T.w i ≫ f i.castSucc
  A : G32JointOrientedTrace R T W eFinal f
  C : G32JointSlicedComponent R T W eFinal
  c : s2e_supportedClass W (s2e_componentCycle C.ι ℚ) R.P.k
  hc : a3b4_IsCycleClass W.hom (s2e_componentCycle C.ι ℚ) R.P.k c

/-- Construct the positive-pair data before invoking either numerical or class-tail input. -/
theorem jointSelectedOrientedPositiveData_exists
    (hstep : by_elab return (← Lean.getConstInfo ``joint_paired_stages_regularity).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (hNonempty : g32p_exponents S ≠ []) :
    Nonempty (G32JointOrientedPositiveData R) := by
  obtain ⟨T⟩ := jointSelectedBase_exists hstep R
  haveI : IsDominant R.β₀.left := n1bc_dominant_of_points_surjective R.β₀
    (n1bc_originalCover_points_surjective R.p₀ R.hpsurj (R.h + 1)
      R.q₀ R.γ R.hγsurj R.β₀ R.hβ₀)
  haveI : IsDominant (R.W₀.left.fromSpecStalk (genericPoint R.W₀.left)) :=
    s2_genericPointMorphism_dominant R.W₀.left
  haveI : IsDominant (T.η 0 ≫ T.e₀.hom.left) := by rw [T.hη₀]; infer_instance
  have hdom₀ : IsDominant (T.η 0) :=
    IsDominant.of_comp_of_isOpenImmersion (T.η 0) T.e₀.hom.left
  let K := fun i : Fin R.r => T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  haveI : ∀ i, IsDominant (T.η i) :=
    s2v_i2b_tower_genericSource_dominant T.B T.b K T.hcartier T.hblowup T.η T.hη hdom₀
  let W := s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r))
  let eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W := Iso.refl W
  let N := fun i => s2b_normalizationOver (T.B i) (T.η i)
  let f := s2e_towerTotalMap N T.eW.hom T.w
  have hf : f 0 = T.eW.hom ∧ ∀ i : Fin R.r, f i.succ = T.w i ≫ f i.castSucc :=
    ⟨s2e_towerTotalMap_zero N T.eW.hom T.w, s2e_towerTotalMap_succ N T.eW.hom T.w⟩
  letI : IsIntegral W.left := by
    change IsIntegral (T.η (Fin.last R.r)).normalization
    infer_instance
  letI : IsProjective W.hom := G32Native.selectedTower_projective S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder W eFinal
  obtain ⟨A⟩ := jointSelectedOrientedTrace_exists R T W eFinal f hf
  obtain ⟨C⟩ := jointSelectedSlicedComponent_exists R T W eFinal hNonempty
  obtain ⟨c, hc, _⟩ := jointSelectedComponentClass_exists R T W eFinal C.toG32JointComponent
  exact ⟨{
    T := T, W := W, eFinal := eFinal, f := f, hf := hf
    A := A, C := C, c := c, hc := hc }⟩

/-- Retain these same positive-pair witnesses for the dependent input fields. -/
def jointSelectedOrientedPositiveData
    (hstep : by_elab return (← Lean.getConstInfo ``joint_paired_stages_regularity).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (hNonempty : g32p_exponents S ≠ []) :
    G32JointOrientedPositiveData R := Classical.choice (jointSelectedOrientedPositiveData_exists hstep R hNonempty)

#print axioms jointSelectedOrientedPositiveData_exists
#print axioms jointSelectedOrientedPositiveData
end ResidueSelected
end HodgeLean.Foundations.Program

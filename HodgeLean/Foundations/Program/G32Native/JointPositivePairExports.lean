import HodgeLean.Foundations.Program.G32Native.JointSelectedBasis
import HodgeLean.Foundations.Program.G32Native.PositivePairNative

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped BigOperators TensorProduct
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.hQ

/-- Pack every positive-pair native field on the retained data and the literal class-tail input. -/
theorem jointPositivePairExports_of_data
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀)
    (A : G32JointTracePackage R T W eFinal f)
    (C : G32JointComponent R T W eFinal)
    (c : s2e_supportedClass W (s2e_componentCycle C.ι ℚ) R.P.k)
    (V : G32JointBasis R T W eFinal f A C c)
    (hf : f 0 = T.eW.hom ∧ ∀ i : Fin R.r, f i.succ = T.w i ≫ f i.castSucc)
    (hclasses : (∀ j,
        let cyc := s2e_rationalOrbitCycle C.ι (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) S.m (V.coeffs j)
        (∀ x ∈ cyc.support, Order.coheight x = R.P.k) ∧
        (∀ x ∈ (a1p_pushforward (eFinal.inv ≫ f (Fin.last R.r)).left cyc).support, Order.coheight x = R.P.k) ∧
        ∃ cr, a3b4_IsCycleClass W.hom cyc R.P.k cr ∧
        ∃ c₀, a3b4_IsCycleClass R.W₀.hom (a1p_pushforward (eFinal.inv ≫ f (Fin.last R.r)).left cyc) R.P.k c₀ ∧
          A.G (s2e_classToAbsolute W cyc R.P.k cr) = V.v j ∧
          s2e_classToAbsolute R.W₀ (a1p_pushforward (eFinal.inv ≫ f (Fin.last R.r)).left cyc) R.P.k c₀ = V.v j)) : Nonempty (PositivePairUnitExports J aut S) := by
  have hExceptional := g32t9_exceptional_primitive S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder R.C₀ J aut R.P R.qC R.jC R.eC R.eZ R.hqC R.hpC R.hχ R.hjC R.primitive R.hprimitive R.hscalar R.hrank R.hselected R.hgenus
  exact ⟨{
    Y := R.Y,
    Z := R.Z,
    W₀ := R.W₀,
    B₀ := R.B₀,
    inst1 := R.inst1,
    inst2 := R.inst2,
    inst3 := R.inst3,
    inst4 := R.inst4,
    inst5 := R.inst5,
    inst6 := R.inst6,
    inst7 := R.inst7,
    inst8 := R.inst8,
    inst9 := R.inst9,
    inst10 := R.inst10,
    inst11 := R.inst11,
    hdimY := R.hdimY,
    hdimZ := R.hdimZ,
    a := R.a,
    e := R.e,
    ha1 := R.ha1,
    hamul := R.hamul,
    hinj := R.hinj,
    p₀ := R.p₀,
    inst12 := R.inst12,
    hp₀ := R.hp₀,
    hpsurj := R.hpsurj,
    hporbit := R.hporbit,
    C := R.C,
    inst13 := R.inst13,
    inst14 := R.inst14,
    inst15 := R.inst15,
    inst16 := R.inst16,
    eY := R.eY,
    hpointAction := R.hpointAction,
    r := R.r,
    σ := R.σ,
    y := R.y,
    rot := R.rot,
    hrot := R.hrot,
    hy := R.hy,
    hbranch := R.hbranch,
    hexp := R.hexp,
    hpair := R.hpair,
    h := R.h,
    hh := R.hh,
    q₀ := R.q₀,
    inst17 := R.inst17,
    hqsurj := R.hqsurj,
    hqinv := R.hqinv,
    hq := R.hq,
    γ := R.γ,
    inst18 := R.inst18,
    hγsurj := R.hγsurj,
    hγinv := R.hγinv,
    hγ := R.hγ,
    β₀ := R.β₀,
    inst19 := R.inst19,
    hβ₀ := R.hβ₀,
    d₀ := R.d₀,
    hd₀ := R.hd₀,
    hgenerator := R.hgenerator,
    B := T.B,
    inst20 := T.inst20,
    inst21 := T.inst21,
    inst22 := T.inst22,
    e₀ := T.e₀,
    b := T.b,
    D := T.D,
    hD₀ := T.hD₀,
    htransform := T.htransform,
    hcartier := T.hcartier,
    hblowup := T.hblowup,
    η := T.η,
    inst23 := T.inst23,
    inst24 := T.inst24,
    hη₀ := T.hη₀,
    hη := T.hη,
    eW := T.eW,
    heW := T.heW,
    hgeneric := T.hgeneric,
    w := T.w,
    hw := T.hw,
    d := T.d,
    hd := T.hd,
    hdinit := T.hdinit,
    hdw := T.hdw,
    horder := T.horder,
    C₀ := R.C₀,
    inst25 := R.inst25,
    inst26 := R.inst26,
    inst27 := R.inst27,
    P := R.P,
    qC := R.qC,
    jC := R.jC,
    eC := R.eC,
    eZ := R.eZ,
    hqC := R.hqC,
    hpC := R.hpC,
    hχ := R.hχ,
    hjC := R.hjC,
    primitive := R.primitive,
    hprimitive := R.hprimitive,
    hscalar := R.hscalar,
    hrank := R.hrank,
    hselected := R.hselected,
    inst28 := R.inst28,
    inst29 := R.inst29,
    hgenus := R.hgenus,
    hExceptionalPrimitive := hExceptional,
    W := W,
    eWr := eFinal,
    f := f,
    h_T12_initial := hf.1,
    h_T12_recursive := hf.2,
    hft := inferInstance,
    hqc := inferInstance,
    hsep := inferInstance,
    hφ := inferInstance,
    trr := A.trr,
    tr₀ := A.tr₀,
    h_T15_final := A.h_T15_final,
    h_T15_initial := A.h_T15_initial,
    h_T16_final_point := A.h_T16_final_point,
    h_T16_initial_point := A.h_T16_initial_point,
    G := A.G,
    h_T18_adjoint := A.h_T18_adjoint,
    h_T18_retraction := A.h_T18_retraction,
    h_T18_deck := A.h_T18_deck,
    Q := C.Q,
    hQ := C.hQ,
    eQ := C.eQ,
    ℓ := C.ℓ,
    ι := C.ι,
    h_T20_slice_immersion := C.h_T20_slice_immersion,
    h_T20_component_immersion := C.h_T20_component_immersion,
    h_T20_square := C.h_T20_square,
    h_T20_avoidance := C.h_T20_avoidance,
    coeffs := V.coeffs,
    v := V.v,
    h_T21_independent := V.h_T21_independent,
    h_T21_span := V.h_T21_span,
    h_T11_T12_P3a_classes := hclasses,
    h_T13_primitive := V.h_T13_primitive
  }⟩

#print axioms jointPositivePairExports_of_data
end HodgeLean.Foundations.Program

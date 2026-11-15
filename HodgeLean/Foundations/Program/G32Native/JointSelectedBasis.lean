import HodgeLean.Foundations.Program.G32Native.JointSelectedTracePackage
import HodgeLean.Foundations.Program.G32Native.JointSelectedComponent
import HodgeLean.Foundations.Program.G32Native.SelectedTowerNumericalOrbitBasis
import HodgeLean.Foundations.Program.G32Native.ExceptionalPrimitive

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
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure G32JointBasis
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀)
    (A : G32JointTracePackage R T W eFinal f)
    (C : G32JointComponent R T W eFinal)
    (c : s2e_supportedClass W (s2e_componentCycle C.ι ℚ) R.P.k) where
  coeffs : Fin (Nat.totient S.m) → Fin S.m → ℚ
  v : Fin (Nat.totient S.m) → (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint R.W₀)) (2 * R.P.k))
  h_T21_independent : LinearIndependent ℚ v
  h_T21_span : Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval (s2e_pullback ℚ R.d₀ (2 * R.P.k)) (Polynomial.cyclotomic S.m ℚ))
  h_T13_primitive : ∀ ζ : ℂ, IsPrimitiveRoot ζ S.m →
        (∃ u : ℂ ⊗[ℚ] (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint R.W₀)) (2 * R.P.k)), u ≠ 0 ∧
          (s2e_pullback ℚ R.d₀ (2 * R.P.k)).baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint R.W₀)) (2 * R.P.k)),
          (s2e_pullback ℚ R.d₀ (2 * R.P.k)).baseChange ℂ u = ζ • u →
          ∃ scalars : Fin (Nat.totient S.m) → ℂ,
            u = ∑ j, scalars j • TensorProduct.tmul ℚ (1 : ℂ) (v j))
  hinverse : ∀ j, v j = A.G (∑ t : Fin S.m, coeffs j t •
    s2e_pullback ℚ ((End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ (S.m - t.val)).asHom)
      (2 * R.P.k) (s2e_classToAbsolute W (s2e_componentCycle C.ι ℚ) R.P.k c))

/-- Apply the numerical paired-component caller with the retained adjoint and tower. -/
theorem jointSelectedBasis_exists
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
    (hf : f 0 = T.eW.hom ∧ ∀ i : Fin R.r, f i.succ = T.w i ≫ f i.castSucc)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle C.ι ℚ) R.P.k c)
    (degree : Cohomology ℚ (TopCat.of (ComplexPoint C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ)
    (hdegree : degree (s2e_normalEuler C.ι R.P.k c) ≠ 0) :
    Nonempty (G32JointBasis R T W eFinal f A C c) := by
  letI := C.h_T20_component_immersion
  have hExceptional := g32t9_exceptional_primitive S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder R.C₀ J aut R.P R.qC R.jC R.eC R.eZ R.hqC R.hpC R.hχ R.hjC R.primitive R.hprimitive R.hscalar R.hrank R.hselected R.hgenus
  obtain ⟨coeffs, v, hi, hs, hinverse, hprimitive⟩ :=
    G32Native.selected_tower_numerical_orbit_basis S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder R.C₀ J aut R.P R.qC R.jC R.eC R.eZ R.hqC R.hpC R.hχ R.hjC R.primitive R.hprimitive R.hscalar R.hrank R.hselected R.hgenus hExceptional W eFinal f hf.1 hf.2
      C.Q C.eQ C.ι c hc C.horbitDisjoint degree hdegree A.G A.h_T18_retraction A.h_T18_deck
  exact ⟨{
    coeffs := coeffs, v := v, h_T21_independent := hi, h_T21_span := hs
    h_T13_primitive := hprimitive, hinverse := hinverse }⟩

#print axioms jointSelectedBasis_exists
end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.JointSelectedBase
import HodgeLean.Foundations.Program.G32Native.PositivePairComponent

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
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure G32JointComponent
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W) where
  Q : Over (Spec ↧ℂ)
  [hQ : IsIntegral Q.left]
  eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))
  ℓ : Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)) ⟶ T.B (Fin.last R.r)
  ι : Q ⟶ W
  h_T20_slice_immersion : IsClosedImmersion ℓ.left
  h_T20_component_immersion : IsClosedImmersion ι.left
  h_T20_square : ι ≫ eFinal.inv ≫ s2b_normalizationMap (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) = eQ.hom ≫ ℓ
  h_T20_avoidance : (∀ t, Disjoint (Set.range ℓ.left) (T.D (Fin.last R.r) t).support)
  horbitImmersion : ∀ t : Fin S.m, IsClosedImmersion
    (ι ≫ (End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ t.val).asHom).left
  horbitDisjoint : ∀ s t : Fin S.m, s ≠ t → Disjoint
    (Set.range (ι ≫ (End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ s.val).asHom).left)
    (Set.range (ι ≫ (End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ t.val).asHom).left)
  horbitUnion : (eFinal.inv ≫ s2b_normalizationMap (T.B (Fin.last R.r)) (T.η (Fin.last R.r))).left ⁻¹'
    Set.range ℓ.left = ⋃ t : Fin S.m,
      Set.range (ι ≫ (End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ t.val).asHom).left

/-- Retain the actual final paired component and its disjoint exhaustive deck orbit. -/
theorem jointSelectedComponent_exists
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (hNonempty : g32p_exponents S ≠ []) : Nonempty (G32JointComponent R T W eFinal) := by
  have hlen := Fintype.card_congr R.σ
  simp only [Fintype.card_fin] at hlen
  have hexp : (g32p_exponents S).length ≠ 0 := by
    intro hzero
    exact hNonempty (List.length_eq_zero_iff.mp hzero)
  have hr : 0 < R.r := by omega
  obtain ⟨Q, hQ, eQ, ℓ, ι, hℓ, hι, hsquare, havoid, himm, hdis, hunion⟩ :=
    g32w_t4_positive_pair_component S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder R.C₀ J aut R.P R.qC R.jC R.eC R.eZ R.hqC R.hpC R.hχ R.hjC R.primitive R.hprimitive R.hscalar R.hrank R.hselected R.hgenus hr W eFinal
  exact ⟨{
    Q := Q, hQ := hQ, eQ := eQ, ℓ := ℓ, ι := ι
    h_T20_slice_immersion := hℓ, h_T20_component_immersion := hι
    h_T20_square := hsquare, h_T20_avoidance := havoid
    horbitImmersion := himm, horbitDisjoint := hdis, horbitUnion := hunion }⟩

#print axioms jointSelectedComponent_exists
end HodgeLean.Foundations.Program

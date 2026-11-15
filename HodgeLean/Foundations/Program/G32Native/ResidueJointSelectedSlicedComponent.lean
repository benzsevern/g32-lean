import HodgeLean.Foundations.Program.G32Native.ProjectiveSliceResidueSpec
import HodgeLean.Foundations.Program.G32Native.JointSelectedComponent
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
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Retain the coherent slice family with the final component.
Source: s2e_projective_slice; Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.5, pp. 13–15. -/
structure G32JointSlicedComponent
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W) extends G32JointComponent R T W eFinal where
  slices : ∀ i, Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)) ⟶ T.B i
  sliceImmersion : ∀ i, IsClosedImmersion (slices i).left
  sliceComp : ∀ i : Fin R.r, slices i.succ ≫ T.b i = slices i.castSucc
  sliceLast : slices (Fin.last R.r) = ℓ
  sliceStrict : ∀ i : Fin R.r, (slices i.succ).left.ker =
    s2c_strictTransform (T.b i).left (slices i.castSucc).left.ker
      (T.D i.castSucc ⟨2*i.val, by omega⟩ ⊔ T.D i.castSucc ⟨2*i.val+1, by omega⟩)
  sliceAvoidance : ∀ (i : Fin (R.r+1)) (t : Fin (2*R.r)), t.val < 2*i.val →
    Disjoint (Set.range (slices i).left) (T.D i t).support
  intersectionsInitial :
    let PP : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ))
    ∀ J : Finset (Fin R.r),
      let K := J.sup (fun i => (T.D 0 ⟨2*i.val, by omega⟩).comap (slices 0).left)
      (J.card ≤ R.P.k → Nonempty (s2c_subscheme PP K ≅
        Over.mk (ProjectiveSpace.toBase (Fin (R.P.k-J.card+1)) (Spec ↧ℂ)))) ∧
      (R.P.k < J.card → IsEmpty (s2c_subscheme PP K).left) ∧
      (∀ x : (s2c_subscheme PP K).left,
        ∃ U : (s2c_subscheme PP K).left.Opens, x ∈ U ∧
          Nonempty (Scheme.Modules.restrict (s2c_conormal (s2c_subschemeι PP K).left) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) : U.toScheme.Modules)))
  pairInitial : ∀ i : Fin R.r,
    (T.D 0 ⟨2*i.val, by omega⟩).comap (slices 0).left =
      (T.D 0 ⟨2*i.val+1, by omega⟩).comap (slices 0).left
  singleInitial : ∀ i : Fin R.r, Nonempty (s2c_subscheme
    (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ)))
    ((T.D 0 ⟨2*i.val, by omega⟩).comap (slices 0).left) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (R.P.k-1+1)) (Spec ↧ℂ)))

  residue : G32InitialResidueData R.Z R.B₀ R.P.k R.r
    (fun t => Point.map R.p₀ (R.eY (R.y (R.σ t)))) (R.hy.comp R.σ.injective)
    (eqToHom (congrArg (g3_power R.Z) R.hselected.symm) ≫ R.γ)
    (slices 0 ≫ T.e₀.hom)
  residueIdeals : ∀ j : Fin R.r,
    (T.D 0 ⟨2 * j.val, by omega⟩).comap (slices 0).left =
      s2e_s2b_residueIdeal R.P.k (residue.indices j) ∧
    (T.D 0 ⟨2 * j.val + 1, by omega⟩).comap (slices 0).left =
      s2e_s2b_residueIdeal R.P.k (residue.indices j)

/-- Retain the actual final paired component and its disjoint exhaustive deck orbit. -/
theorem jointSelectedSlicedComponent_exists
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ))
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (hNonempty : g32p_exponents S ≠ []) : Nonempty (G32JointSlicedComponent R T W eFinal) := by
  have hlen := Fintype.card_congr R.σ
  simp only [Fintype.card_fin] at hlen
  have hexp : (g32p_exponents S).length ≠ 0 := by
    intro hzero
    exact hNonempty (List.length_eq_zero_iff.mp hzero)
  have hr : 0 < R.r := by omega
  obtain ⟨ℓ, himm, hfac, hstrict, hpairSlice, hintersections, havoidAll, residue, hresidue⟩ :=
    s2e_projective_slice_residue_spec S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder R.C₀ J aut R.P R.qC R.jC R.eC R.eZ R.hqC R.hpC R.hχ R.hjC R.primitive R.hprimitive R.hscalar R.hrank R.hselected R.hgenus hr
  letI : IsClosedImmersion (ℓ (Fin.last R.r)).left := himm _
  have havoid : ∀ t, Disjoint (Set.range (ℓ (Fin.last R.r)).left)
      (T.D (Fin.last R.r) t).support := by
    intro t
    exact havoidAll (Fin.last R.r) t (by simpa using t.isLt)
  obtain ⟨Q, eQ, ι, hι, hsquare, horbitImm, hdisjoint, hexhaust⟩ :=
    s2e_chain_component_orbit
    (S := S) (Y := R.Y) (Z := R.Z) (W₀ := R.W₀)
    (B₀ := R.B₀) (hdimY := R.hdimY) (hdimZ := R.hdimZ) (a := R.a)
    (e := R.e) (ha1 := R.ha1) (hamul := R.hamul) (hinj := R.hinj)
    (p₀ := R.p₀) (hp₀ := R.hp₀) (hpsurj := R.hpsurj) (hporbit := R.hporbit)
    (C := R.C) (eY := R.eY) (hpointAction := R.hpointAction) (r := R.r)
    (σ := R.σ) (y := R.y) (rot := R.rot) (hrot := R.hrot)
    (hy := R.hy) (hbranch := R.hbranch) (hexp := R.hexp) (hpair := R.hpair)
    (h := R.h) (hh := R.hh) (q₀ := R.q₀) (hqsurj := R.hqsurj)
    (hqinv := R.hqinv) (hq := R.hq) (γ := R.γ) (hγsurj := R.hγsurj)
    (hγinv := R.hγinv) (hγ := R.hγ) (β₀ := R.β₀) (hβ₀ := R.hβ₀)
    (d₀ := R.d₀) (hd₀ := R.hd₀) (hgenerator := R.hgenerator) (B := T.B)
    (e₀ := T.e₀) (b := T.b) (D := T.D) (hD₀ := T.hD₀)
    (htransform := T.htransform) (hcartier := T.hcartier) (hblowup := T.hblowup) (η := T.η)
    (hη₀ := T.hη₀) (hη := T.hη) (eW := T.eW) (heW := T.heW)
    (hgeneric := T.hgeneric) (w := T.w) (hw := T.hw) (d := T.d)
    (hd := T.hd) (hdinit := T.hdinit) (hdw := T.hdw) (horder := T.horder)
    (W := W) (eFinal := eFinal.symm) (k := R.P.k) (ℓ := ℓ (Fin.last R.r))
    (havoid := havoid)
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ))).left :=
    IntersectionProductScaf_projective_integral R.P.k
  haveI : IsIntegral Q.left := IsIntegral.of_isIso eQ.inv.left
  refine ⟨{
    Q := Q, hQ := inferInstance, eQ := eQ, ℓ := ℓ (Fin.last R.r), ι := ι
    h_T20_slice_immersion := himm _, h_T20_component_immersion := hι
    h_T20_square := ?_, h_T20_avoidance := havoid
    horbitImmersion := horbitImm, horbitDisjoint := hdisjoint, horbitUnion := ?_
    slices := ℓ, sliceImmersion := himm, sliceComp := hfac, sliceLast := rfl
    sliceStrict := hstrict, sliceAvoidance := havoidAll, intersectionsInitial := hintersections
    pairInitial := hpairSlice, singleInitial := ?_
    residue := residue, residueIdeals := hresidue }⟩
  · simpa only [Iso.symm_hom, Category.assoc] using hsquare
  · ext x
    simpa only [Iso.symm_hom, Iso.symm_inv, Set.mem_preimage, Set.mem_iUnion] using hexhaust x
  · intro i
    have hk : 0 < R.P.k := by have := R.hh; have := R.hselected; omega
    have hsingle := (hintersections {i}).1
      (by simpa only [Finset.card_singleton] using (Nat.succ_le_of_lt hk))
    rw [Finset.card_singleton, Finset.sup_singleton] at hsingle
    exact hsingle

#print axioms jointSelectedSlicedComponent_exists
end ResidueSelected
end HodgeLean.Foundations.Program

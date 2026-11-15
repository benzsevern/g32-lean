import HodgeLean.Foundations.Program.SchoenTransferJ2NativeInput
import HodgeLean.Foundations.Program.SchoenTransferJ12NativeMap
import HodgeLean.Foundations.Program.SchoenTransferJ12TowerCurveCycles
import HodgeLean.Foundations.Program.SchoenTransferJ1ZeroPairProofs
import HodgeLean.Foundations.Program.SchoenTransferJ1Row5Proofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local irreducible] s4_invariantPrimitive cfd_cycleSpan homPullback

variable {A : g32t_Sixfold} (X : g32p_Cover A)

/-- Assemble the supplier fields from the retained native curve witnesses. -/
theorem s4_selected_native_supplier :
    (by_elab do
      let j ← Lean.Elab.Term.elabTerm (← `(X.J)) none
      let gr ← Lean.Elab.Term.elabTerm (← `((inferInstance : GrpObj X.J))) none
      let co ← Lean.Elab.Term.elabTerm (← `((inferInstance : IsCommMonObj X.J))) none
      let it ← Lean.Elab.Term.elabTerm (← `((inferInstance : IsIntegral X.J.left))) none
      let sm ← Lean.Elab.Term.elabTerm (← `((inferInstance : Smooth X.J.hom))) none
      let pr ← Lean.Elab.Term.elabTerm (← `((inferInstance : IsProjective X.J.hom))) none
      let act ← Lean.Elab.Term.elabTerm (← `(X.aut)) none
      let args := #[j, gr, co, it, sm, pr, act]
      let mut ty := (← Lean.getConstInfo ``s4_chain_native_input_identity).type
      for _ in [:7] do ty := ty.bindingBody!
      let input := ty.bindingDomain!.instantiateRev args
      let output ← Lean.Elab.Term.elabTerm (← `(g32p_SchoenSupplier X)) none
      Lean.mkArrow input output) := by
  intro hNative
  have hall : ∀ S (hS : g32p_Admissible X.aut S),
      cyc_Algebraic (cupProductOf (X.part S hS).P)
        (X.part S hS).act.cyc_coordinates := by
    intro S hS
    have hData := hNative S hS
    rcases hData with hTower | hCanonical
    ·
      rcases hTower with ⟨Y, hTower⟩
      rcases hTower with ⟨Z, hTower⟩
      rcases hTower with ⟨W₀, hTower⟩
      rcases hTower with ⟨B₀, hTower⟩
      rcases hTower with ⟨inst1, hTower⟩
      letI := inst1
      rcases hTower with ⟨inst2, hTower⟩
      letI := inst2
      rcases hTower with ⟨inst3, hTower⟩
      letI := inst3
      rcases hTower with ⟨inst4, hTower⟩
      letI := inst4
      rcases hTower with ⟨inst5, hTower⟩
      letI := inst5
      rcases hTower with ⟨inst6, hTower⟩
      letI := inst6
      rcases hTower with ⟨inst7, hTower⟩
      letI := inst7
      rcases hTower with ⟨inst8, hTower⟩
      letI := inst8
      rcases hTower with ⟨inst9, hTower⟩
      letI := inst9
      rcases hTower with ⟨inst10, hTower⟩
      letI := inst10
      rcases hTower with ⟨inst11, hTower⟩
      letI := inst11
      rcases hTower with ⟨hdimY, hTower⟩
      rcases hTower with ⟨hdimZ, hTower⟩
      rcases hTower with ⟨a, hTower⟩
      rcases hTower with ⟨e, hTower⟩
      rcases hTower with ⟨ha1, hTower⟩
      rcases hTower with ⟨hamul, hTower⟩
      rcases hTower with ⟨hinj, hTower⟩
      rcases hTower with ⟨p₀, hTower⟩
      rcases hTower with ⟨inst12, hTower⟩
      letI := inst12
      rcases hTower with ⟨hp₀, hTower⟩
      rcases hTower with ⟨hpsurj, hTower⟩
      rcases hTower with ⟨hporbit, hTower⟩
      rcases hTower with ⟨C, hTower⟩
      rcases hTower with ⟨inst13, hTower⟩
      letI := inst13
      rcases hTower with ⟨inst14, hTower⟩
      letI := inst14
      rcases hTower with ⟨inst15, hTower⟩
      letI := inst15
      rcases hTower with ⟨inst16, hTower⟩
      letI := inst16
      rcases hTower with ⟨eY, hTower⟩
      rcases hTower with ⟨hpointAction, hTower⟩
      rcases hTower with ⟨r, hTower⟩
      rcases hTower with ⟨σ, hTower⟩
      rcases hTower with ⟨y, hTower⟩
      rcases hTower with ⟨rot, hTower⟩
      rcases hTower with ⟨hrot, hTower⟩
      rcases hTower with ⟨hy, hTower⟩
      rcases hTower with ⟨hbranch, hTower⟩
      rcases hTower with ⟨hexp, hTower⟩
      rcases hTower with ⟨hpair, hTower⟩
      rcases hTower with ⟨h, hTower⟩
      rcases hTower with ⟨hh, hTower⟩
      rcases hTower with ⟨q₀, hTower⟩
      rcases hTower with ⟨inst17, hTower⟩
      letI := inst17
      rcases hTower with ⟨hqsurj, hTower⟩
      rcases hTower with ⟨hqinv, hTower⟩
      rcases hTower with ⟨hq, hTower⟩
      rcases hTower with ⟨γ, hTower⟩
      rcases hTower with ⟨inst18, hTower⟩
      letI := inst18
      rcases hTower with ⟨hγsurj, hTower⟩
      rcases hTower with ⟨hγinv, hTower⟩
      rcases hTower with ⟨hγ, hTower⟩
      rcases hTower with ⟨β₀, hTower⟩
      rcases hTower with ⟨inst19, hTower⟩
      letI := inst19
      rcases hTower with ⟨hβ₀, hTower⟩
      rcases hTower with ⟨d₀, hTower⟩
      rcases hTower with ⟨hd₀, hTower⟩
      rcases hTower with ⟨hgenerator, hTower⟩
      rcases hTower with ⟨B, hTower⟩
      rcases hTower with ⟨inst20, hTower⟩
      letI := inst20
      rcases hTower with ⟨inst21, hTower⟩
      letI := inst21
      rcases hTower with ⟨inst22, hTower⟩
      letI := inst22
      rcases hTower with ⟨e₀, hTower⟩
      rcases hTower with ⟨b, hTower⟩
      rcases hTower with ⟨D, hTower⟩
      rcases hTower with ⟨hD₀, hTower⟩
      rcases hTower with ⟨htransform, hTower⟩
      rcases hTower with ⟨hcartier, hTower⟩
      rcases hTower with ⟨hblowup, hTower⟩
      rcases hTower with ⟨η, hTower⟩
      rcases hTower with ⟨inst23, hTower⟩
      letI := inst23
      rcases hTower with ⟨inst24, hTower⟩
      letI := inst24
      rcases hTower with ⟨hη₀, hTower⟩
      rcases hTower with ⟨hη, hTower⟩
      rcases hTower with ⟨eW, hTower⟩
      rcases hTower with ⟨heW, hTower⟩
      rcases hTower with ⟨hgeneric, hTower⟩
      rcases hTower with ⟨w, hTower⟩
      rcases hTower with ⟨hw, hTower⟩
      rcases hTower with ⟨d, hTower⟩
      rcases hTower with ⟨hd, hTower⟩
      rcases hTower with ⟨hdinit, hTower⟩
      rcases hTower with ⟨hdw, hTower⟩
      rcases hTower with ⟨horder, hTower⟩
      rcases hTower with ⟨C₀, hTower⟩
      rcases hTower with ⟨inst25, hTower⟩
      letI := inst25
      rcases hTower with ⟨inst26, hTower⟩
      letI := inst26
      rcases hTower with ⟨inst27, hTower⟩
      letI := inst27
      rcases hTower with ⟨P, hTower⟩
      rcases hTower with ⟨qC, hTower⟩
      rcases hTower with ⟨jC, hTower⟩
      rcases hTower with ⟨eC, hTower⟩
      rcases hTower with ⟨eZ, hTower⟩
      rcases hTower with ⟨hqC, hTower⟩
      rcases hTower with ⟨hpC, hTower⟩
      rcases hTower with ⟨hχ, hTower⟩
      rcases hTower with ⟨hjC, hTower⟩
      rcases hTower with ⟨primitive, hTower⟩
      rcases hTower with ⟨hprimitive, hTower⟩
      rcases hTower with ⟨hscalar, hTower⟩
      rcases hTower with ⟨hrank, hTower⟩
      rcases hTower with ⟨hselected, hTower⟩
      rcases hTower with ⟨inst28, hTower⟩
      letI := inst28
      rcases hTower with ⟨inst29, hTower⟩
      letI := inst29
      rcases hTower with ⟨hgenus, hTower⟩
      rcases hTower with ⟨hExceptionalPrimitive, hTower⟩
      rcases hTower with ⟨W, hTower⟩
      rcases hTower with ⟨eWr, hTower⟩
      obtain ⟨powIntegral, powSmooth, powProjective, hCurve⟩ := s4_selected_tower_curve_cycles S Y Z W₀ B₀ hdimY hdimZ
        a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction
        r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq
        γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀
        htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd
        hdinit hdw horder C₀ X.J X.aut P qC jC eC eZ hqC hpC hχ hjC primitive
        hprimitive hscalar hrank hselected hgenus hExceptionalPrimitive W eWr hTower
      letI := powIntegral
      letI := powSmooth
      letI := powProjective
      have hamul' : ∀ u v, a (u * v) = a u ≫ a v := by
        intro u v
        have huv : u * v = v * u := e.injective (by
          simp only [map_mul]
          exact mul_comm _ _)
        rw [huv, hamul]
      obtain ⟨N, fmap, hN, hfmap, hfinj, hfimage, hfscalar⟩ :=
        s4_selected_native_curve_map X.J X.aut S P Y C₀ hdimY a e C
          eC.toEquiv eY.toEquiv qC jC hqC primitive hprimitive hscalar
      exact s4_chain_selected_part_cycles_aux X S hS P Y hdimY a e hχ ha1
        hamul' hinj fmap hfinj hfimage hfscalar hCurve
    ·
      rcases hCanonical with ⟨Y, hCanonical⟩
      rcases hCanonical with ⟨Z, hCanonical⟩
      rcases hCanonical with ⟨W₀, hCanonical⟩
      rcases hCanonical with ⟨B₀, hCanonical⟩
      rcases hCanonical with ⟨inst1, hCanonical⟩
      letI := inst1
      rcases hCanonical with ⟨inst2, hCanonical⟩
      letI := inst2
      rcases hCanonical with ⟨inst3, hCanonical⟩
      letI := inst3
      rcases hCanonical with ⟨inst4, hCanonical⟩
      letI := inst4
      rcases hCanonical with ⟨inst5, hCanonical⟩
      letI := inst5
      rcases hCanonical with ⟨inst6, hCanonical⟩
      letI := inst6
      rcases hCanonical with ⟨inst7, hCanonical⟩
      letI := inst7
      rcases hCanonical with ⟨inst8, hCanonical⟩
      letI := inst8
      rcases hCanonical with ⟨inst9, hCanonical⟩
      letI := inst9
      rcases hCanonical with ⟨inst10, hCanonical⟩
      letI := inst10
      rcases hCanonical with ⟨inst11, hCanonical⟩
      letI := inst11
      rcases hCanonical with ⟨hdimY, hCanonical⟩
      rcases hCanonical with ⟨hdimZ, hCanonical⟩
      rcases hCanonical with ⟨a, hCanonical⟩
      rcases hCanonical with ⟨e, hCanonical⟩
      rcases hCanonical with ⟨ha1, hCanonical⟩
      rcases hCanonical with ⟨hamul, hCanonical⟩
      rcases hCanonical with ⟨hinj, hCanonical⟩
      rcases hCanonical with ⟨p₀, hCanonical⟩
      rcases hCanonical with ⟨inst12, hCanonical⟩
      letI := inst12
      rcases hCanonical with ⟨hp₀, hCanonical⟩
      rcases hCanonical with ⟨hpsurj, hCanonical⟩
      rcases hCanonical with ⟨hporbit, hCanonical⟩
      rcases hCanonical with ⟨C, hCanonical⟩
      rcases hCanonical with ⟨inst13, hCanonical⟩
      letI := inst13
      rcases hCanonical with ⟨inst14, hCanonical⟩
      letI := inst14
      rcases hCanonical with ⟨inst15, hCanonical⟩
      letI := inst15
      rcases hCanonical with ⟨inst16, hCanonical⟩
      letI := inst16
      rcases hCanonical with ⟨eY, hCanonical⟩
      rcases hCanonical with ⟨hpointAction, hCanonical⟩
      rcases hCanonical with ⟨r, hCanonical⟩
      rcases hCanonical with ⟨σ, hCanonical⟩
      rcases hCanonical with ⟨y, hCanonical⟩
      rcases hCanonical with ⟨rot, hCanonical⟩
      rcases hCanonical with ⟨hrot, hCanonical⟩
      rcases hCanonical with ⟨hy, hCanonical⟩
      rcases hCanonical with ⟨hbranch, hCanonical⟩
      rcases hCanonical with ⟨hexp, hCanonical⟩
      rcases hCanonical with ⟨hpair, hCanonical⟩
      rcases hCanonical with ⟨h, hCanonical⟩
      rcases hCanonical with ⟨hh, hCanonical⟩
      rcases hCanonical with ⟨q₀, hCanonical⟩
      rcases hCanonical with ⟨inst17, hCanonical⟩
      letI := inst17
      rcases hCanonical with ⟨hqsurj, hCanonical⟩
      rcases hCanonical with ⟨hqinv, hCanonical⟩
      rcases hCanonical with ⟨hq, hCanonical⟩
      rcases hCanonical with ⟨γ, hCanonical⟩
      rcases hCanonical with ⟨inst18, hCanonical⟩
      letI := inst18
      rcases hCanonical with ⟨hγsurj, hCanonical⟩
      rcases hCanonical with ⟨hγinv, hCanonical⟩
      rcases hCanonical with ⟨hγ, hCanonical⟩
      rcases hCanonical with ⟨β₀, hCanonical⟩
      rcases hCanonical with ⟨inst19, hCanonical⟩
      letI := inst19
      rcases hCanonical with ⟨hβ₀, hCanonical⟩
      rcases hCanonical with ⟨d₀, hCanonical⟩
      rcases hCanonical with ⟨hd₀, hCanonical⟩
      rcases hCanonical with ⟨hgenerator, hCanonical⟩
      rcases hCanonical with ⟨C₀, hCanonical⟩
      rcases hCanonical with ⟨inst20, hCanonical⟩
      letI := inst20
      rcases hCanonical with ⟨inst21, hCanonical⟩
      letI := inst21
      rcases hCanonical with ⟨inst22, hCanonical⟩
      letI := inst22
      rcases hCanonical with ⟨P, hCanonical⟩
      rcases hCanonical with ⟨qC, hCanonical⟩
      rcases hCanonical with ⟨jC, hCanonical⟩
      rcases hCanonical with ⟨eC, hCanonical⟩
      rcases hCanonical with ⟨eZ, hCanonical⟩
      rcases hCanonical with ⟨hqC, hCanonical⟩
      rcases hCanonical with ⟨hpC, hCanonical⟩
      rcases hCanonical with ⟨hχ, hCanonical⟩
      rcases hCanonical with ⟨hjC, hCanonical⟩
      rcases hCanonical with ⟨primitive, hCanonical⟩
      rcases hCanonical with ⟨hprimitive, hCanonical⟩
      rcases hCanonical with ⟨hscalar, hCanonical⟩
      rcases hCanonical with ⟨hrank, hCanonical⟩
      rcases hCanonical with ⟨hselected, hCanonical⟩
      rcases hCanonical with ⟨inst23, hCanonical⟩
      letI := inst23
      rcases hCanonical with ⟨inst24, hCanonical⟩
      letI := inst24
      rcases hCanonical with ⟨hgenus, hCanonical⟩
      rcases hCanonical with ⟨hr, hCanonical⟩
      have hSupport := s4_chain_selected_zero_pair_supported_basis_aux
        S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit
        C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj
        hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator C₀ X.J X.aut P
        qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected
        hgenus hr hCanonical
      obtain ⟨het, hZ, lineMap, hLine, hAbelLine, sliceQ, hSliceIntegral,
        hSliceSmooth, hSliceProjective, sliceIso, sliceι, hSlice, hComponent,
        hDisjoint, hPreimage, hConormal, baseClass, hBaseClass, hHyperplane,
        hyperplaneClass, hHyperplaneClass, hEuler, hNonzero, hWeighted,
        coeff, basisv, hli, hspan, hclasses, heigen⟩ := hSupport
      letI := hZ
      letI := hSliceIntegral
      letI := hSliceSmooth
      letI := hSliceProjective
      let powIntegral : IsIntegral (g3_power Y (2 * P.k)).left :=
        spec_g3b_isIntegral_power Y (2 * P.k)
      let powSmooth : Smooth (g3_power Y (2 * P.k)).hom := spec_g3_smooth_power Y (2 * P.k)
      let powProjective : IsProjective (g3_power Y (2 * P.k)).hom :=
        spec_g3c_isProjective_power Y (2 * P.k)
      letI := powIntegral
      letI := powSmooth
      letI := powProjective
      have hCurve := s4_selected_quotient_basis_cycles S Y hdimY (h + 1) P.k
        P.act.cyc_positive hh hselected a e ha1 hamul W₀ q₀ hqsurj hqinv hq d₀
        hgenerator basisv hspan (by
          intro i
          exact ⟨s2e_rationalOrbitCycle sliceι d₀ S.m (coeff i),
            (hclasses i).1, (hclasses i).2⟩)
      have hamul' : ∀ u v, a (u * v) = a u ≫ a v := by
        intro u v
        have huv : u * v = v * u := e.injective (by
          simp only [map_mul]
          exact mul_comm _ _)
        rw [huv, hamul]
      obtain ⟨N, fmap, hN, hfmap, hfinj, hfimage, hfscalar⟩ :=
        s4_selected_native_curve_map X.J X.aut S P Y C₀ hdimY a e C
          eC.toEquiv eY.toEquiv qC jC hqC primitive hprimitive hscalar
      exact s4_chain_selected_part_cycles_aux X S hS P Y hdimY a e hχ ha1
        hamul' hinj fmap hfinj hfimage hfscalar hCurve
  exact ⟨fun S hS _ => hall S hS, fun S hS _ => hall S hS⟩

#print axioms s4_selected_native_supplier
end HodgeLean.Foundations.Program

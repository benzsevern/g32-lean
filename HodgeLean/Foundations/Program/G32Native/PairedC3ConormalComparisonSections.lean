import HodgeLean.Foundations.Program.G32Native.PairedC3PullbackSectionComposition

/-! # Original ideal sections under the natural conormal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback
namespace HodgeLean.Foundations.Program.G32Native

/-- The natural conormal comparison carries the original pulled-back
ideal section to the class of its actual scalar-extended ideal image. -/
theorem paired_c3_conormal_comparison_section
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f)
    (U : W.Opens) (s : Γ(Conormal.idealModule i, U)) :
    (Conormal.comparisonMap i i' f g h).app ((g ≫ i) ⁻¹ᵁ U)
      (eta g (Conormal.sheaf i) (i ⁻¹ᵁ U) (eta i (Conormal.idealModule i) U s)) =
      pairedC3ModuleRestrict (Conormal.sheaf i')
        ((congrArg (fun p : Q' ⟶ W => p ⁻¹ᵁ U) h).le)
        (eta i' (Conormal.idealModule i') (f ⁻¹ᵁ U)
          ((Conormal.idealPullbackMap i i' f g h).app (f ⁻¹ᵁ U)
            (eta f (Conormal.idealModule i) U s))) := by
  let I := Conormal.idealModule i
  let L := (g ≫ i) ⁻¹ᵁ U
  let R := (i' ≫ f) ⁻¹ᵁ U
  let hl : L ≤ R := (congrArg (fun p : Q' ⟶ W => p ⁻¹ᵁ U) h).le
  let A := (Scheme.Modules.pullbackComp g i).app I
  let B := (Scheme.Modules.pullbackCongr h).app I
  let C := (Scheme.Modules.pullbackComp i' f).app I
  let D := (Scheme.Modules.pullback i').map (Conormal.idealPullbackMap i i' f g h)
  let t := eta i' ((Scheme.Modules.pullback f).obj I) (f ⁻¹ᵁ U) (eta f I U s)
  have hA := paired_c3_pullback_composition_section g i I U s
  have hB := paired_c3_pullback_congr_section h I U s
  have hC := paired_c3_pullback_composition_section i' f I U s
  have hc := congrArg (C.inv.app R) hC
  have hi := congrArg (fun φ => φ.val.app (Opposite.op R) t) C.hom_inv_id
  have hC' : C.inv.app R (eta (i' ≫ f) I U s) = t := hc.symm.trans hi
  have hD := paired_c3_pullback_morphism_section i'
    (Conormal.idealPullbackMap i i' f g h) (f ⁻¹ᵁ U) (eta f I U s)
  have hn := PresheafOfModules.naturality_apply (C.inv ≫ D).val
    (homOfLE hl).op (eta (i' ≫ f) I U s)
  have h₁ := congrArg (fun z => D.app L (C.inv.app L (B.hom.app L z))) hA
  have h₂ := congrArg (fun z => D.app L (C.inv.app L z)) hB
  have h₃ := congrArg (fun z => pairedC3ModuleRestrict (Conormal.sheaf i') hl (D.app R z)) hC'
  have h₄ := congrArg (pairedC3ModuleRestrict (Conormal.sheaf i') hl) hD
  have heq : Conormal.comparisonMap i i' f g h = A.hom ≫ B.hom ≫ C.inv ≫ D := by
    dsimp only [A, B, C, D, Conormal.comparisonMap]
    erw [← paired_c3_pullback_congr_hom_app h I]
    rfl
  have hh := congrArg (fun φ => φ.app L
    (eta g (Conormal.sheaf i) (i ⁻¹ᵁ U) (eta i I U s))) heq
  exact hh.trans (h₁.trans (h₂.trans (hn.trans (h₃.trans h₄))))

/-- The scalar-extended ideal section is the original ideal section
map obtained by transposing the natural comparison. -/
theorem paired_c3_ideal_pullback_section
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f)
    (U : W.Opens) (s : Γ(Conormal.idealModule i, U)) :
    (Conormal.idealPullbackMap i i' f g h).app (f ⁻¹ᵁ U)
      (eta f (Conormal.idealModule i) U s) =
        (Conormal.idealPushforwardMap i i' f g h).app U s := by
  have hη := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply
    (Conormal.idealPushforwardMap i i' f g h)
  exact congrArg (fun φ => φ.val.app (Opposite.op U) s) hη

end HodgeLean.Foundations.Program.G32Native

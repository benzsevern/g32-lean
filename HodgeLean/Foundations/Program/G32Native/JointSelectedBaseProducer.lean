import HodgeLean.Foundations.Program.G32Native.JointSelectedBase
import HodgeLean.Foundations.Program.G32Native.JointSelectedPairedFamily
import HodgeLean.Foundations.Program.G32Native.PairedBaseNative
import HodgeLean.Foundations.Program.G32Native.SelectedGenericLifts
import HodgeLean.Foundations.Program.G32Native.SelectedInitialNormalization
import HodgeLean.Foundations.Program.G32Native.NormalizationTower
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericCharts
import HodgeLean.Foundations.Program.SchoenTowerI2bTowerGeneric
import HodgeLean.Foundations.Program.SchoenCycleC1PeriodicDeckAutHelpers

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
open G32Native

/-- Construct the paired base and normalization tower on the shared selected prefix. -/
theorem jointSelectedBase_exists
    (hstep : by_elab return (← Lean.getConstInfo ``joint_paired_stages_regularity).type.bindingDomain!)
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) : Nonempty (G32JointBase R) := by
  classical
  letI := R.inst1
  letI := R.inst2
  letI := R.inst3
  letI := R.inst4
  letI := R.inst5
  letI := R.inst6
  letI := R.inst7
  letI := R.inst8
  letI := R.inst9
  letI := R.inst10
  letI := R.inst11
  letI := R.inst12
  letI := R.inst13
  letI := R.inst14
  letI := R.inst15
  letI := R.inst16
  letI := R.inst17
  letI := R.inst18
  letI := R.inst19
  letI := R.inst25
  letI := R.inst26
  letI := R.inst27
  letI := R.inst28
  letI := R.inst29
  obtain ⟨B, hBi, hBs, hBp, e₀, b, D, hD₀, htransform, hcartier, hblowup, _⟩ :=
    g32t6_paired_base_native R.Z R.B₀ R.h R.r R.γ
      (fun t => Point.map R.p₀ (R.eY (R.y (R.σ t))))
      (joint_selected_paired_family hstep R.Y R.Z R.B₀ R.hdimZ R.h R.r
        R.γ R.hγinv R.hγ R.p₀ (rsq_Quot S.χ.ker R.C) R.eY R.y R.σ R.hy)
  letI := hBi
  letI := hBs
  letI := hBp
  have hcentre (i : Fin R.r) :
      (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩).support ≠ ⊤ :=
    s2v_i2a_center_support_ne_top (b i).left _ (hcartier i)
  haveI : IsDominant R.β₀.left := n1bc_dominant_of_points_surjective R.β₀
    (n1bc_originalCover_points_surjective R.p₀ R.hpsurj (R.h + 1)
      R.q₀ R.γ R.hγsurj R.β₀ R.hβ₀)
  obtain ⟨η, hηqc, hηqs, hη₀, hη⟩ :=
    selectedGenericLifts R.W₀ R.B₀ R.r B R.β₀ e₀ b D hcentre hblowup
  letI := hηqc
  letI := hηqs
  obtain ⟨eW, heW, hgeneric⟩ :=
    g32w_selected_initial_normalization S R.Y R.W₀ R.B₀ R.a R.e R.ha1 R.hamul
      R.h R.q₀ R.hqinv R.hq R.β₀ R.r B e₀ η hη₀
  haveI : IsDominant (R.W₀.left.fromSpecStalk (genericPoint R.W₀.left)) :=
    s2_genericPointMorphism_dominant R.W₀.left
  haveI : IsDominant (η 0 ≫ e₀.hom.left) := by rw [hη₀]; infer_instance
  have hdom₀ : IsDominant (η 0) :=
    IsDominant.of_comp_of_isOpenImmersion (η 0) e₀.hom.left
  let K := fun i : Fin R.r => D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    D i.castSucc ⟨2 * i.val + 1, by omega⟩
  haveI : ∀ i, IsDominant (η i) :=
    s2v_i2b_tower_genericSource_dominant B b K hcartier hblowup η hη hdom₀
  have horder₀ : End.of R.d₀ ^ S.m = 1 := End.ext R.horder₀
  haveI : IsIso R.d₀ :=
    (isUnit_iff_isIso _).mp (IsUnit.of_pow_eq_one horder₀ (NeZero.ne S.m))
  obtain ⟨w, hw, d, hd, hdinit, hdw, horder⟩ :=
    g32w_normalization_tower S R.W₀ R.B₀ R.β₀ R.d₀ R.hd₀ horder₀
      R.r B e₀ b K hcentre hblowup η hη₀ hη eW hgeneric
  exact ⟨{
    B := B, e₀ := e₀, b := b, D := D, hD₀ := hD₀
    htransform := htransform, hcartier := hcartier, hblowup := hblowup
    η := η, hη₀ := hη₀, hη := hη, eW := eW, heW := heW, hgeneric := hgeneric
    w := w, hw := hw, d := d, hd := hd, hdinit := hdinit, hdw := hdw, horder := horder }⟩

#print axioms jointSelectedBase_exists
end HodgeLean.Foundations.Program

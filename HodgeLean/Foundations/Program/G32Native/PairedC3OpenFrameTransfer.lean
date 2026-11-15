import HodgeLean.Foundations.Program.G32Native.PairedC3OpenPullbackSections
import HodgeLean.Foundations.Program.G32Native.PairedC3SynthesisTransfer
import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteFrameCoordinates

/-! # Canonical finite section frames through original open immersion charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A canonical frame on an affine chart source transfers back to every
original subopen of the chart range, keeping the original generators. -/
theorem paired_c3_open_frame_transfer {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) {σ : Type} [Fintype σ]
    (U : Y.Opens) (hU : U ≤ f.opensRange) (hpre : f ⁻¹ᵁ U = ⊤)
    (g : σ → Γ(M, U))
    (hframe : ∀ W : X.Opens, Function.Bijective (pairedC3FiniteFrameSynthesis
      (fun a => pairedC3ModuleRestrict ((Scheme.Modules.pullback f).obj M) hpre.ge
        (pairedC3PullbackSection f M U (g a))) W le_top))
    (V : Y.Opens) (hV : V ≤ U) :
    Function.Bijective (pairedC3FiniteFrameSynthesis g V hV) := by
  let M' := (Scheme.Modules.pullback f).obj M
  let w := fun a => pairedC3ModuleRestrict M' hpre.ge (pairedC3PullbackSection f M U (g a))
  have hgw (a : σ) : pairedC3PullbackSection f M V (pairedC3ModuleRestrict M hV (g a)) =
      pairedC3ModuleRestrict M' le_top (w a) := by
    have hn := paired_c3_pullback_section_restrict f M U V hV (g a)
    have hs := paired_c3_module_restrict_comp M' hpre.ge
      (le_top : f ⁻¹ᵁ V ≤ ⊤) (pairedC3PullbackSection f M U (g a))
    exact hn.trans hs.symm
  letI : IsIso (f.app V) := f.isIso_app V (hV.trans hU)
  exact paired_c3_synthesis_bijective_transfer (f.app V).hom
    (ConcreteCategory.bijective_of_isIso (f.app V))
    (pairedC3PullbackSection f M V) (paired_c3_open_pullback_section_bijective f M V (hV.trans hU))
    (paired_c3_pullback_section_smul f M V)
    (fun a => pairedC3ModuleRestrict M hV (g a))
    (fun a => pairedC3ModuleRestrict M' le_top (w a)) hgw (hframe (f ⁻¹ᵁ V))

#print axioms paired_c3_open_frame_transfer
end HodgeLean.Foundations.Program.G32Native

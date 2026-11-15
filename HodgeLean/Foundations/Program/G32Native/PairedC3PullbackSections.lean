import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs

/-! # Original sections through the canonical module pullback unit -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)

/-- Pull an original module section through the canonical pullback adjunction unit. -/
def pairedC3PullbackSection (U : Y.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U).hom

/-- The canonical pulled section retains the original structural scalar map. -/
theorem paired_c3_pullback_section_smul (U : Y.Opens) (c : Γ(Y, U)) (s : Γ(M, U)) :
    pairedC3PullbackSection f M U (c • s) =
      f.app U c • pairedC3PullbackSection f M U s := by
  exact Scheme.Modules.Hom.app_smul
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) c s

/-- Canonical section pullback commutes with the original inverse-image restrictions. -/
theorem paired_c3_pullback_section_restrict (U V : Y.Opens) (hVU : V ≤ U) (s : Γ(M, U)) :
    pairedC3PullbackSection f M V (M.presheaf.map (homOfLE hVU).op s) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun x hx => hVU hx)).op
          (pairedC3PullbackSection f M U s) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE hVU).op s


/-- Canonical section pullback commutes with the original module morphism. -/
theorem paired_c3_pullback_section_naturality {N : Y.Modules} (φ : M ⟶ N)
    (U : Y.Opens) (s : Γ(M, U)) :
    pairedC3PullbackSection f N U (φ.app U s) =
      ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U)
        (pairedC3PullbackSection f M U s) := by
  have h := congrArg (fun t : M ⟶ (Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj N) => t.app U s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)
  exact h

#print axioms paired_c3_pullback_section_naturality
#print axioms pairedC3PullbackSection
#print axioms paired_c3_pullback_section_smul
#print axioms paired_c3_pullback_section_restrict
end HodgeLean.Foundations.Program.G32Native

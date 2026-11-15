import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonComposition
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.PullbackFrame

/-! # Composition of original pullback sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback
namespace HodgeLean.Foundations.Program.G32Native

/-- The geometric pullback-composition comparison preserves the section
obtained from the original adjunction units. -/
theorem paired_c3_pullback_composition_section
    {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (eta f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (eta g M U s)) =
        eta (f ≫ g) M U s := by
  let E := (Scheme.Modules.pullbackComp f g).app M
  have h := Conormal.pullbackComp_inv_transpose f g M
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) (𝟙 _)
  erw [Category.comp_id, Adjunction.homEquiv_id] at h
  have hs := congrArg (fun φ => φ.val.app (Opposite.op U) s) h
  change E.inv.app ((f ≫ g) ⁻¹ᵁ U) (eta (f ≫ g) M U s) =
    eta f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (eta g M U s) at hs
  have hi := congrArg (fun φ => φ.val.app (Opposite.op ((f ≫ g) ⁻¹ᵁ U))
    (eta (f ≫ g) M U s)) E.inv_hom_id
  exact (congrArg (E.hom.app ((f ≫ g) ⁻¹ᵁ U)) hs.symm).trans hi

/-- Equality transport of scheme maps preserves their original
pullback sections and the corresponding equality of inverse-image opens. -/
theorem paired_c3_pullback_congr_section
    {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app (f ⁻¹ᵁ U) (eta f M U s) =
      pairedC3ModuleRestrict ((Scheme.Modules.pullback g).obj M)
        ((congrArg (fun p : X ⟶ Y => p ⁻¹ᵁ U) h).le) (eta g M U s) := by
  cases h
  simp [Scheme.Modules.pullbackCongr, pairedC3ModuleRestrict]

/-- A pulled-back module morphism preserves the section induced by
the original geometric adjunction unit. -/
theorem paired_c3_pullback_morphism_section
    {X Y : Scheme.{0}} (f : X ⟶ Y) {M N : Y.Modules} (u : M ⟶ N)
    (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map u).app (f ⁻¹ᵁ U) (eta f M U s) =
      eta f N U (u.app U s) := by
  exact (congrArg (fun φ => φ.val.app (Opposite.op U) s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality u)).symm

/-- The component of pullback congruence is the literal equality
transport of the original pulled-back module. -/
theorem paired_c3_pullback_congr_hom_app
    {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg (fun p : X ⟶ Y => (Scheme.Modules.pullback p).obj M) h) := by
  cases h
  rfl

end HodgeLean.Foundations.Program.G32Native

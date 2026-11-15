import HodgeLean.Foundations.Curves.Picard.LineBundles.CartierIdeal
import HodgeLean.Foundations.Curves.Picard.LineBundles.SectionMaps

/-! # Sheaf frames from regular local equations

Affine ideal coordinates determine actual sections of the categorical kernel.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The actual kernel section corresponding to an element of the affine ideal. -/
def idealSection {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) : Γ(idealModule I, U.1) :=
  (idealAffineSectionsEquiv I U).symm ⟨a, ha⟩

theorem idealSection_coordinate {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U) :
    ((idealAffineSectionsEquiv I U) (idealSection I U a ha)).val = a := by
  exact congrArg Subtype.val ((idealAffineSectionsEquiv I U).apply_symm_apply ⟨a, ha⟩)

theorem idealSectionHom_inclusion {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U)
    (V : U.1.toScheme.Opens) (r : Γ(U.1.toScheme, V)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
      (Opposite.op (U.1.ι ''ᵁ V))
        ((localSectionHom (idealModule I) U.1 (idealSection I U a ha)).val.app
          (Opposite.op V) r) =
      (U.1.ι.appIso V).inv r *
        X.presheaf.map (homOfLE (U.1.ι_image_le V)).op a := by
  rw [localSectionHom_app]
  rw [map_smul]
  have hn := PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val
    (homOfLE (U.1.ι_image_le V)).op (idealSection I U a ha)
  change (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
      (Opposite.op (U.1.ι ''ᵁ V))
      ((idealModule I).presheaf.map (homOfLE (U.1.ι_image_le V)).op (idealSection I U a ha)) =
    X.presheaf.map (homOfLE (U.1.ι_image_le V)).op
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op U.1) (idealSection I U a ha)) at hn
  rw [hn, ← idealAffineSectionsEquiv_val, idealSection_coordinate]
  rfl

/-- A regular principal equation trivializes the actual ideal module on its neighbourhood. -/
def idealLocalGeneratorIso {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (a : Γ(X, U.1)) (ha : IsRegular a) (hI : I.ideal U = Ideal.span {a}) :
    (idealModule I).restrict U.1.ι ≅ unit U.1.toScheme := by
  have haI : a ∈ I.ideal U := by rw [hI]; exact Ideal.mem_span_singleton_self a
  let f := localSectionHom (idealModule I) U.1 (idealSection I U a haI)
  haveI : IsIso f := by
    apply module_isIso_of_affine_app f
    intro V
    let W : X.affineOpens := ⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩
    have hWU : W ≤ U := U.1.ι_image_le V.1
    let aW := X.presheaf.map (homOfLE (show W.1 ≤ U.1 from hWU)).op a
    have hIW : I.ideal W = Ideal.span {aW} := by
      rw [← I.map_ideal hWU, hI, Ideal.map_span]
      simp only [Set.image_singleton]
      rfl
    let g := idealAffineGeneratorEquiv I W aW (regular_restrict_affine U W hWU a ha) hIW
    have hfg (r : Γ(U.1.toScheme, V.1)) :
        f.app V.1 r = g ((U.1.ι.appIso V.1).inv r) := by
      apply (idealAffineSectionsEquiv I W).injective
      apply Subtype.ext
      rw [idealAffineSectionsEquiv_val]
      change (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
        (Opposite.op (U.1.ι ''ᵁ V.1))
          ((localSectionHom (idealModule I) U.1 (idealSection I U a haI)).val.app
            (Opposite.op V.1) r) = _
      rw [idealSectionHom_inclusion]
      exact (idealAffineGeneratorEquiv_coordinate I W aW
        (regular_restrict_affine U W hWU a ha) hIW _).symm
    have hg : Function.Bijective (fun r : Γ(U.1.toScheme, V.1) =>
        g ((U.1.ι.appIso V.1).inv r)) :=
      g.bijective.comp (ConcreteCategory.bijective_of_isIso (U.1.ι.appIso V.1).inv)
    change Function.Bijective (fun r => f.app V.1 r)
    rw [show (fun r => f.app V.1 r) = _ from funext hfg]
    exact hg
  exact (asIso f).symm

/-- The actual Cartier kernel ideal of a divisor family is a line. -/
def familyIdealLine (C T : Over (Spec ↧ℂ)) {n : ℕ} (D : Families.Family C T n) :
    Line (Families.Product C T) where
  module := idealModule D.ideal
  trivial x := by
    obtain ⟨U, hx, a, ha, hI⟩ := D.localEquation x
    exact ⟨U.1, hx, ⟨idealLocalGeneratorIso D.ideal U a ha hI⟩⟩

end HodgeLean.Foundations.Curves.Picard.LineBundles

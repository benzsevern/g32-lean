import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenPushforwardNatIso

/-! # Values of the open direct image identification -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- On sections, open direct image comparison is transport along the preimage equality. -/
lemma unionConormalOpenPushforward_hom_apply
    {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules)
    (V : U.toScheme.Opens)
    (m : Γ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj M), V)) :
    (((unionConormalOpenPushforwardNatIso f U).hom.app M).app V) m =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
        (show Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) from m) := rfl

end HodgeLean.Foundations.Program.G32Native

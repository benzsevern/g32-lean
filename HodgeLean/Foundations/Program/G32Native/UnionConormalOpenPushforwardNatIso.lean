import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenPushforwardIso

/-! # Naturality of open restriction and direct image -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- Direct image commutes naturally with ambient open restriction. -/
def unionConormalOpenPushforwardNatIso {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) := by
  refine NatIso.ofComponents (fun M => unionConormalOpenPushforwardIso f U M) ?_
  intro M N φ
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  let m₀ : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) := m
  change N.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
      (φ.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) m₀) =
    φ.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))
      (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op m₀)
  have hn := CategoryTheory.congr_fun
    (((Scheme.Modules.toPresheaf X).map φ).naturality
      (eqToHom (image_morphismRestrict_preimage f U V)).op) m₀
  exact hn.symm

end HodgeLean.Foundations.Program.G32Native

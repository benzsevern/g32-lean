import HodgeLean.Foundations.Program.SchoenQuotientStalks

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Injectivity on source stalks is preserved by restriction to a target open. -/
theorem s2_morphismRestrict_stalkMap_injective {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : ∀ x : X, Function.Injective (f.stalkMap x)) (U : Y.Opens)
    (x : (f ⁻¹ᵁ U).toScheme) : Function.Injective ((f ∣_ U).stalkMap x) := by
  have hi : Function.Injective (((f ⁻¹ᵁ U).ι ≫ f).stalkMap x) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (asIso ((f ⁻¹ᵁ U).ι.stalkMap x)).commRingCatIsoToRingEquiv.injective.comp (hf x.val)
  rw [← morphismRestrict_ι f U, Scheme.Hom.stalkMap_comp] at hi
  let e := (asIso (U.ι.stalkMap ((f ∣_ U) x))).commRingCatIsoToRingEquiv
  intro a b hab
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  exact congrArg e (hi hab)

set_option backward.isDefEq.respectTransparency.types false in
/-- A surjective morphism with injective source stalk maps remains an epimorphism
on every target open. -/
theorem s2_morphismRestrict_epi {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (hf : ∀ x : X, Function.Injective (f.stalkMap x)) (U : Y.Opens) : Epi (f ∣_ U) := by
  haveI : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict (inferInstance : Surjective f) U
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ (inferInstance : Surjective (f ∣_ U)).surj
  intro x
  apply ConcreteCategory.mono_of_injective
  exact s2_morphismRestrict_stalkMap_injective f hf U x

/-- Every target-open restriction of the global invariant projection is an epimorphism. -/
theorem s2_gluedQuotientMap_restrict_epi (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U : (s2_invariantAffineGlued X G ρ).Opens) :
    Epi (s2_gluedQuotientMap X G ρ hcover ∣_ U) := by
  haveI : Surjective (s2_gluedQuotientMap X G ρ hcover) :=
    ⟨s2_gluedQuotientMap_surjective X G ρ hcover⟩
  exact s2_morphismRestrict_epi _ (s2_gluedQuotientMap_stalkMap_injective X G ρ hcover) U

end HodgeLean.Foundations.Program

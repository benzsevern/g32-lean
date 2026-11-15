import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphSupportCap

/-! # Actual support cap injectivity through original ambient homeomorphisms
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual pulled-back collar cap detects the original target cap through the literal supported cohomology and support homology maps of an ambient homeomorphism.
Source: ProperCycleSupportCollar.cap_comapHomeomorph; TopPair.isoOfSubset; homologyMap_comp.
HC no distance; AV milestone no distance. -/
lemma properCycle_support_cap_injective_of_comapHomeomorph
    {X Y : TopCat.{0}} {S : Set X} {T : Set Y}
    (C : ProperCycleSupportCollar Y T) (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ S ↔ e x ∈ T) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (c : Homology ℚ X (p+q))
    (hinj : Function.Injective ((C.comapHomeomorph e he).cap hS p q c)) :
    Function.Injective (C.cap hT p q
      (homologyMap ℚ (p+q) (TopCat.ofHom ⟨e, e.continuous⟩) c)) := by
  let P : TopPair.ofSubset (X := X) Sᶜ ≅ TopPair.ofSubset (X := Y) Tᶜ :=
    TopPair.isoOfSubset e (fun x => not_congr (he x).symm)
  let F : CohomologyWithSupport ℚ Y T p ≅ CohomologyWithSupport ℚ X S p :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) p).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso P))
  let H : S ≃ₜ T := e.subtype he
  let s : TopCat.of S ⟶ TopCat.of T := TopCat.ofHom ⟨H, H.continuous⟩
  let si : TopCat.of T ⟶ TopCat.of S := TopCat.ofHom ⟨H.symm, H.symm.continuous⟩
  have hsi : s ≫ si = 𝟙 (TopCat.of S) := by
    ext x : 1
    exact H.symm_apply_apply x
  have hs : Function.Injective (homologyMap ℚ q s) := by
    apply Function.LeftInverse.injective (g := homologyMap ℚ q si)
    intro z
    change ((homologyMap ℚ q si).comp (homologyMap ℚ q s)) z = z
    rw [← homologyMap_comp, hsi, homologyMap_id, LinearMap.id_apply]
  intro a b hab
  apply F.toLinearEquiv.injective
  apply hinj
  apply hs
  have ha := C.cap_comapHomeomorph e he hS hT p q a c
  have hb := C.cap_comapHomeomorph e he hS hT p q b c
  exact ha.trans (hab.trans hb.symm)

end HodgeLean.Foundations.QuotientDuality

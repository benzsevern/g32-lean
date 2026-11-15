import HodgeLean.Foundations.QuotientDuality.ProperCycleHomeomorphSupportCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Original supported cap naturality through actual ambient homeomorphisms
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Pulling back the actual collar through an ambient homeomorphism retains its original supported cap square, with literal support and complement-pair maps.
Source: properCycle_retracted_neighborhood_cap_naturality; ProperCycleSupportCollar.comapHomeomorph.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_comapHomeomorph
    {X Y : TopCat.{0}} {S : Set X} {T : Set Y}
    (C : ProperCycleSupportCollar Y T) (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ S ↔ e x ∈ T) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (a : CohomologyWithSupport ℚ Y T p) (c : Homology ℚ X (p+q)) :
    homologyMap ℚ q
      (TopCat.ofHom ⟨fun s : S => (⟨e s.val, (he s.val).mp s.property⟩ : T), by fun_prop⟩)
      ((C.comapHomeomorph e he).cap hS p q c
        (relativeCohomologyMap ℚ p
          (TopPair.ofSubsetHom (TopCat.ofHom ⟨e, e.continuous⟩)
            (show Set.MapsTo e Sᶜ Tᶜ from fun x hx h => hx ((he x).mpr h))) a)) =
      C.cap hT p q (homologyMap ℚ (p+q) (TopCat.ofHom ⟨e, e.continuous⟩) c) a := by
  let D := C.comapHomeomorph e he
  let f : TopPair.ofSubset (X := X) Sᶜ ⟶ TopPair.ofSubset (X := Y) Tᶜ :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx h => hx ((he x).mpr h))
  let u : TopCat.of D.neighborhood ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨e x.val, x.property⟩, by fun_prop⟩
  let g : neighborhoodSupportComplementPair D.neighborhood S ⟶
      neighborhoodSupportComplementPair C.neighborhood T :=
    TopPair.ofSubsetHom u (fun x hx h => hx ((he x.val).mpr h))
  let s : TopCat.of S ⟶ TopCat.of T :=
    TopCat.ofHom ⟨fun x => ⟨e x.val, (he x.val).mp x.property⟩, by fun_prop⟩
  have hsquare : g ≫ b6m_subspacePairMap Y C.neighborhood Tᶜ =
      b6m_subspacePairMap X D.neighborhood Sᶜ ≫ f := by ext x : 2 <;> rfl
  have hsupport : D.inclusion ≫ TopPair.Hom.fst g = s ≫ C.inclusion := by
    ext x : 1
    apply Subtype.ext
    exact (ConcreteCategory.congr_hom C.inclusion_factor (s x)).symm
  exact properCycle_retracted_neighborhood_cap_naturality X Y S T D.neighborhood C.neighborhood
    hS hT D.isOpen C.isOpen D.contains C.contains f g hsquare D.inclusion C.inclusion
    D.retraction C.retraction s hsupport C.inclusion_retraction D.deformation p q a c

end HodgeLean.Foundations.QuotientDuality

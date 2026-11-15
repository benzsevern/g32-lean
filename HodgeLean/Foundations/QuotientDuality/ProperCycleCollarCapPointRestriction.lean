import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRestrictedCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarLocalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarAmbientInverse
import HodgeLean.Foundations.QuotientDuality.ProperCycleNestedPointOrientation

/-! # Actual global collar cap point values on arbitrary smaller neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual global supported cap has its original point value on every smaller collar neighborhood, using literal supported restriction and inverse point excision of the specified ambient local orientation.
Source: ProperCycleSupportCollar.cap_point_local; ProperCycleSupportCollar.restricted_point_cap_naturality; properCycle_nested_point_orientation.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_point_restriction
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S)
    (hS : IsClosed S) (W : Opens X) (hWN : (W : Set X) ⊆ C.neighborhood)
    (z : S) (hzW : z.val ∈ W) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p+q)) :
    let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
      TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
    let r := TopPair.ofSubsetHom (i ≫ C.retraction)
      (show Set.MapsTo (i ≫ C.retraction)
        ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) {z}ᶜ from fun _ h => h)
    localOrientation (TopCat.of S) q (C.cap hS p q c a) z =
      relativeHomologyMap ℚ q r
        (triadCapCohomologyLinear ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
          ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) p q
          (relativeCohomologyMap ℚ p (b6m_subspacePairMap X (W : Set X) Sᶜ) a)
          ((C.restricted_point_triad_iso hS W hWN z hzW (p+q)).inv.hom
            ((properCycle_open_local_homology_iso X W ⟨z.val, hzW⟩ (p+q)).inv.hom
              (localOrientation X (p+q) c z.val)))) := by
  dsimp only
  let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let aN := relativeCohomologyMap ℚ p (b6m_subspacePairMap X C.neighborhood Sᶜ) a
  let cW := (properCycle_open_local_homology_iso X W ⟨z.val, hzW⟩ (p+q)).inv.hom
    (localOrientation X (p+q) c z.val)
  have hj : (C.inclusion z).val = z.val := by
    have h := ConcreteCategory.congr_hom C.inclusion_factor (z : TopCat.of S)
    exact h
  have ho := properCycle_nested_point_orientation X W ⟨C.neighborhood, C.isOpen⟩ hWN
    ⟨z.val, hzW⟩ (C.inclusion z) hj.symm (p+q) c
  have h := C.restricted_point_cap_naturality hS W hWN z hzW p q aN cW
  let KW := triadCapCohomologyLinear ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
    ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) p q
  let KN := triadCapCohomologyLinear ℚ (TopCat.of C.neighborhood) (Subtype.val ⁻¹' Sᶜ)
    (C.retraction ⁻¹' {z}ᶜ) p q
  let r := TopPair.ofSubsetHom (i ≫ C.retraction)
    (show Set.MapsTo (i ≫ C.retraction)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) {z}ᶜ from fun _ h => h)
  let fA := TopPair.ofSubsetHom i (show Set.MapsTo i (Subtype.val ⁻¹' Sᶜ)
    (Subtype.val ⁻¹' Sᶜ) from fun _ h => h)
  have hp : fA ≫ b6m_subspacePairMap X C.neighborhood Sᶜ =
      b6m_subspacePairMap X (W : Set X) Sᶜ := by ext x : 2 <;> rfl
  have ha : relativeCohomologyMap ℚ p fA aN =
      relativeCohomologyMap ℚ p (b6m_subspacePairMap X (W : Set X) Sᶜ) a := by
    dsimp only [aN]
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hp]
    rfl
  have h2 := congrArg (fun u => relativeHomologyMap ℚ q (C.pointPairMap z)
    (KN aN ((C.pointTriadIso hS z (p+q)).inv.hom u))) ho
  have hga := congrArg (fun b => relativeHomologyMap ℚ q r
    (KW b ((C.restricted_point_triad_iso hS W hWN z hzW (p+q)).inv.hom cW))) ha
  have hg := C.cap_point_local hS z p q a c
  have hg2 := congrArg (fun u => relativeHomologyMap ℚ q (C.pointPairMap z) (KN aN u))
    (C.point_ambient_inverse hS z (p+q) (localOrientation X (p+q) c (C.inclusion z).val))
  exact hg.trans (hg2.trans ((h.trans h2).symm.trans hga))

end HodgeLean.Foundations.QuotientDuality

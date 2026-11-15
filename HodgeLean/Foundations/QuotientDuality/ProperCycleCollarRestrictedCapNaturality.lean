import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarRestrictedPointIso
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalCapNaturality

/-! # Actual cap restriction to smaller collar point triads
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Restriction of the original collar point cap to an actual smaller open neighborhood retains the original retraction and the actual ambient point map.
Source: properCycle_local_triad_cap_naturality; ProperCycleSupportCollar.restricted_point_triad_union.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.restricted_point_cap_naturality
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S)
    (hS : IsClosed S) (W : Opens X) (hWN : (W : Set X) ⊆ C.neighborhood)
    (z : S) (hzW : z.val ∈ W) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of C.neighborhood)
      (Subtype.val ⁻¹' Sᶜ)) p)
    (c : orientationGroup (TopCat.of W) (p+q) ⟨z.val, hzW⟩) :
    let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
      TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
    let hj : (C.inclusion z).val = z.val := by
      have h := ConcreteCategory.congr_hom C.inclusion_factor (z : TopCat.of S)
      exact h
    let hf : Set.MapsTo i ({⟨z.val, hzW⟩} : Set W)ᶜ
        ({C.inclusion z} : Set C.neighborhood)ᶜ := fun x hx he =>
      hx (Subtype.ext ((congrArg Subtype.val he).trans hj))
    let r := TopPair.ofSubsetHom (i ≫ C.retraction)
      (show Set.MapsTo (i ≫ C.retraction)
        ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) {z}ᶜ from fun _ h => h)
    relativeHomologyMap ℚ q r
      (triadCapCohomologyLinear ℚ (TopCat.of W) (Subtype.val ⁻¹' Sᶜ)
        ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) p q
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom i (show Set.MapsTo i
          (Subtype.val ⁻¹' Sᶜ) (Subtype.val ⁻¹' Sᶜ) from fun _ h => h)) a)
        ((C.restricted_point_triad_iso hS W hWN z hzW (p+q)).inv.hom c)) =
    relativeHomologyMap ℚ q (C.pointPairMap z)
      (triadCapCohomologyLinear ℚ (TopCat.of C.neighborhood) (Subtype.val ⁻¹' Sᶜ)
        (C.retraction ⁻¹' {z}ᶜ) p q a
        ((C.pointTriadIso hS z (p+q)).inv.hom
          (relativeHomologyMap ℚ (p+q) (TopPair.ofSubsetHom i hf) c))) := by
  dsimp only
  let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hj : (C.inclusion z).val = z.val := by
    have h := ConcreteCategory.congr_hom C.inclusion_factor (z : TopCat.of S)
    exact h
  have hf : Set.MapsTo i ({⟨z.val, hzW⟩} : Set W)ᶜ
      ({C.inclusion z} : Set C.neighborhood)ᶜ := fun x hx he =>
    hx (Subtype.ext ((congrArg Subtype.val he).trans hj))
  have hA : Set.MapsTo i (Subtype.val ⁻¹' Sᶜ) (Subtype.val ⁻¹' Sᶜ) := fun _ h => h
  have hB : Set.MapsTo i
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ)
      (C.retraction ⁻¹' {z}ᶜ) := fun _ h => h
  have h := properCycle_local_triad_cap_naturality i _ _ _ _ hA hB
    (hS.isOpen_compl.preimage continuous_subtype_val)
    (isClosed_singleton.isOpen_compl.preimage (C.retraction.hom.continuous.comp i.hom.continuous))
    (hS.isOpen_compl.preimage continuous_subtype_val)
    (isClosed_singleton.isOpen_compl.preimage C.retraction.hom.continuous)
    ⟨z.val, hzW⟩ (C.inclusion z) (C.restricted_point_triad_union W hWN z hzW)
    (C.point_triad_union z) hf p q a c
  have hp : TopPair.ofSubsetHom i hB ≫ C.pointPairMap z =
      TopPair.ofSubsetHom (i ≫ C.retraction)
        (show Set.MapsTo (i ≫ C.retraction)
          ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) {z}ᶜ from fun _ h => h) := by
    ext x : 2 <;> rfl
  have hh := congrArg (relativeHomologyMap ℚ q (C.pointPairMap z)) h
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hp] at hh
  exact hh

end HodgeLean.Foundations.QuotientDuality

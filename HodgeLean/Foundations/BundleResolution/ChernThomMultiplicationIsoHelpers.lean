import HodgeLean.Foundations.BundleResolution.ChernBundleProjectedCapHelpers
import HodgeLean.Foundations.BundleThom.EmptyPairCoclassHelpers

/-! # Actual Thom multiplication from global projected cap

Universal coefficients identify multiplication by the independently selected
Thom class with the dual of its actual projected cap map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)

theorem i1_complexBundleThomMultiplication_bijective_of_projected_cap (n : ℕ)
    (hcap : Function.Bijective (i1_complexBundleThomCapToBase E n)) :
    Function.Bijective (i1_complexBundleThomMultiplication E n) := by
  let P := TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ
  let a := cohomologyEquivDualHomology ℚ (TopCat.of B) n
  let b := relativeCohomologyEquivDualHomology ℚ P (2 * k + n)
  let c := i1_complexBundleThomCapToBase E n
  have he : i1_complexBundleThomMultiplication E n =
      b.symm.toLinearMap.comp (c.dualMap.comp a.toLinearMap) := by
    apply LinearMap.ext
    intro α
    apply b.injective
    apply LinearMap.ext
    intro z
    change b (i1_complexBundleThomMultiplication E n α) z =
      b (b.symm (c.dualMap (a α))) z
    rw [b.apply_symm_apply]
    exact i1_complexBundleThomCapToBase_pairing E n α z
  have hd : Function.Bijective c.dualMap := LinearMap.dualMap_bijective_iff.mpr hcap
  rw [he]
  exact b.symm.bijective.comp (hd.comp a.bijective)

theorem i1_complexBundleThomMultiplication_bijective (n : ℕ) :
    Function.Bijective (i1_complexBundleThomMultiplication E n) := by
  cases isEmpty_or_nonempty B with
  | inl hB =>
    letI := hB
    let P := TopPair.ofSubset (X := i1_totalSpace k E.fibre) (i1_zeroSupport k E.fibre)ᶜ
    letI : IsEmpty (TotalSpace (Fin k → ℂ) E.fibre) :=
      ⟨fun v => isEmptyElim v.proj⟩
    letI : IsEmpty P.fst := by
      change IsEmpty (TotalSpace (Fin k → ℂ) E.fibre)
      infer_instance
    letI : Subsingleton (Cohomology ℚ (TopCat.of B) n) :=
      ⟨fun x y => (cohomology_eq_zero_of_isEmpty (TopCat.of B) n x).trans
        (cohomology_eq_zero_of_isEmpty (TopCat.of B) n y).symm⟩
    letI : Subsingleton (RelativeCohomology ℚ P (2 * k + n)) :=
      i1_relativeCohomology_subsingleton_of_isEmpty P _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr hB =>
    letI := hB
    exact i1_complexBundleThomMultiplication_bijective_of_projected_cap E n
      (i1_complexBundleThomCapToBase_bijective E n)

end HodgeLean.Foundations.BundleResolution

import HodgeLean.Foundations.RationalHomologyManifold.CapNaturality
import HodgeLean.Foundations.QuotientDuality.LocalZeroOrientation
import HodgeLean.Foundations.QuotientDuality.LocalZeroDuality

/-! The degree-zero case and point localization on singleton spaces.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.RealDefs
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Localization on a singleton is injective in every degree.
Source: Hatcher, Algebraic Topology, section 2.1, homology relative to the empty subspace.
HC no distance; AV milestone no distance.
-/
theorem singleton_localization_injective (X : TopCat.{0}) [Subsingleton X]
    (n : ℕ) (x : X) : Function.Injective (fun c => localization X n c x) := by
  let P := pointComplementPair x
  letI : IsIso (relativeChainProjection ℚ P) := isIso_relativeChainProjection _
    ⟨fun y => y.property (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))⟩
  letI : IsIso (relativeHomologyProjection ℚ P n) := by
    unfold relativeHomologyProjection
    infer_instance
  exact ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso (relativeHomologyProjection ℚ P n))).1

/-- Cap against a nonzero degree-zero class is bijective on a path-connected space.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, degree-zero homology and the cap unit.
HC no distance; AV milestone no distance.
-/
theorem cap_zero_bijective (X : TopCat.{0}) [PathConnectedSpace X]
    (c : Homology ℚ X 0) (hc : c ≠ 0) :
    Function.Bijective (localTraceCap X 0 0 c) := by
  let u : Cohomology ℚ X 0 := HodgeLean.Foundations.Singular.unit X
  let e : Homology ℚ X 0 →ₗ[ℚ] ℚ := cohomologyEquivDualHomology ℚ X 0 u
  have he : e c ≠ 0 := singular_unit_evaluation_ne_zero X c hc
  have hei : Function.Injective e := by
    intro v w hvw
    apply sub_eq_zero.mp
    by_contra hne
    apply singular_unit_evaluation_ne_zero X (v - w) hne
    exact (map_sub e v w).trans (sub_eq_zero.mpr hvw)
  have hu : localTraceCap X 0 0 c u = c := by
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
    intro l
    obtain ⟨b, rfl⟩ := (cohomologyEquivDualHomology ℚ X 0).surjective l
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [u, HodgeLean.Foundations.Singular.one_cup] using
      cap_evaluation X 0 0 c u b
  constructor
  · intro a b hab
    obtain ⟨r, rfl⟩ := exists_smul_singular_unit X a
    obtain ⟨s, rfl⟩ := exists_smul_singular_unit X b
    have hrs : r = s := by
      have hh := congrArg e hab
      change e (localTraceCap X 0 0 c (r • u)) =
        e (localTraceCap X 0 0 c (s • u)) at hh
      simp only [map_smul, hu, smul_eq_mul] at hh
      exact (mul_right_cancel₀ he) hh
    rw [hrs]
  · intro z
    refine ⟨(e z / e c) • u, ?_⟩
    rw [map_smul, hu]
    apply hei
    rw [map_smul]
    exact div_mul_cancel₀ _ he

#print axioms singleton_localization_injective
#print axioms cap_zero_bijective
end HodgeLean.Foundations.RationalHomologyManifold

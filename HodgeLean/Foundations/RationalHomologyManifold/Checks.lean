import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.QuotientDuality.SphereOrientationGeometry
import HodgeLean.Foundations.QuotientDuality.RetainedTraceChecks
import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility

/-! # Independent sphere normalization and cap tests

All witnesses use actual singular classes. No new statement or Proofs module
is imported. The inherited sphere geometry has checked bodies.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold.Checks

private abbrev S := TopCat.of (OnePoint ℂ)
private def triangulation : FiniteTriangulation S := by
  let K := sphere_finite_triangulation.choose
  exact ⟨3, K, sphere_finite_triangulation.choose_spec.1,
    sphere_finite_triangulation.choose_spec.2.some⟩

private def c : Homology ℚ S 2 := sphere_surface_fundamental.choose
private theorem c_local : localization S 2 c = sphereLocalOrientation.generator :=
  funext sphere_surface_fundamental.choose_spec.1
private theorem local_ne (x : S) : sphereLocalOrientation.generator x ≠ 0 := by
  intro hz
  have h := (sphereLocalOrientation.generates x).1
    (show LinearMap.toSpanSingleton ℚ _ (sphereLocalOrientation.generator x) (0 : ℚ) =
      LinearMap.toSpanSingleton ℚ _ (sphereLocalOrientation.generator x) (1 : ℚ) by simp [hz])
  exact zero_ne_one h
private theorem c_ne : c ≠ 0 := by
  intro hz
  have h := congrFun c_local (OnePoint.infty : S)
  rw [hz, map_zero] at h
  exact local_ne _ h.symm
private theorem double_ne {V : Type} [AddCommGroup V] [Module ℚ V]
    {v : V} (hv : v ≠ 0) : (2 : ℚ) • v ≠ v := by
  intro he
  have h : v + v = v + 0 := by simpa only [two_smul, add_zero] using he
  exact hv (add_left_cancel h)

/-- Rescaling the sphere class breaks its specified local normalization.
Source: Hatcher, section 3.3, Theorem 3.26.
HC no distance; AV milestone no distance.
-/
theorem exists_falsification :
    ∃ t : FiniteTriangulation S,
      localization S 2 c = sphereLocalOrientation.generator ∧
      localization S 2 ((2 : ℚ) • c) ≠ sphereLocalOrientation.generator := by
  refine ⟨triangulation, c_local, ?_⟩
  intro he
  have h := congrFun he (OnePoint.infty : S)
  rw [map_smul] at h
  change (2 : ℚ) • localization S 2 c _ = _ at h
  rw [c_local] at h
  exact double_ne (local_ne _) h

example := exists_falsification

/-- Dropping the common local normalization permits distinct top classes.
Source: Hatcher, Theorem 3.26.
HC no distance; AV milestone no distance.
-/
theorem uniqueness_falsification : c ≠ (2 : ℚ) • c ∧
    localization S 2 c ≠ localization S 2 ((2 : ℚ) • c) := by
  refine ⟨(double_ne c_ne).symm, ?_⟩
  intro he
  apply exists_falsification.choose_spec.2
  exact he.symm.trans c_local

example := uniqueness_falsification

private theorem unit_cap :
    localTraceCap S 0 2 c (HodgeLean.Foundations.Singular.unit S) = c := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro f
  obtain ⟨b, rfl⟩ := (cohomologyEquivDualHomology ℚ S 2).surjective f
  rw [map_sub]
  apply sub_eq_zero.mpr
  change localTracePairing S 0 2 c (HodgeLean.Foundations.Singular.unit S) b = _
  have h := congrArg (fun z => cohomologyEquivDualHomology ℚ S 2 z c)
    (localTraceCup_eq_singularCup S 0 2 (HodgeLean.Foundations.Singular.unit S) b)
  change cohomologyEquivDualHomology ℚ S 2
    ((cohomologyEquivDualHomology ℚ S 2).symm _) c = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.trans (congrArg (fun z => cohomologyEquivDualHomology ℚ S 2 z c)
    (HodgeLean.Foundations.Singular.one_cup S b))

/-- Replacing the normalized class by zero destroys injectivity of the actual cap map.
Source: Hatcher, Theorem 3.30.
HC no distance; AV milestone no distance.
-/
theorem cap_falsification :
    localTraceCap S 0 2 c (HodgeLean.Foundations.Singular.unit S) ≠ 0 ∧
      ¬ Function.Injective (localTraceCap S 0 2 (0 : Homology ℚ S 2)) := by
  refine ⟨by rw [unit_cap]; exact c_ne, ?_⟩
  intro hi
  have h := hi (show localTraceCap S 0 2 (0 : Homology ℚ S 2)
      (HodgeLean.Foundations.Singular.unit S) = localTraceCap S 0 2 0 0 by
    simp [localTraceCap])
  exact HodgeLean.Foundations.Singular.unit_ne_zero S h

example := cap_falsification

private abbrev G := OnePoint ℂ ≃ₜ OnePoint ℂ
private def reflection : G := Complex.conjCLE.toHomeomorph.onePointCongr

/-- An actual nonidentity orientation-reversing sphere map cannot preserve the global class.
Source: Hatcher, sections 2.2 and 3.3; the checked rational sphere reflection calculation.
HC no distance; AV milestone no distance.
-/
theorem homeomorph_falsification :
    ∃ d : Homology ℚ S 2,
      homologyMap ℚ 2 (deckMap G S reflection) d ≠ d := by
  obtain ⟨_, _, _, _, a, K, hK, eK, o, d, u, hd, hu, hm, hne⟩ :=
    RetainedTraceChecks.local_deck_trace_pairing_sphere_falsification
  refine ⟨d, ?_⟩
  intro he
  apply hne
  change cohomologyEquivDualHomology ℚ S 2
    (cohomologyMap ℚ 2 (deckMap G S reflection) u) d = _
  rw [cohomologyEquivDualHomology_cohomologyMap, he]
  rfl

example := homeomorph_falsification

/-- A factor two on the target cap map fails on a nonzero sphere class.
Source: Hatcher, section 3.3, cap naturality.
HC no distance; AV milestone no distance.
-/
theorem cap_naturality_falsification :
    localTraceCap S 0 2 c (HodgeLean.Foundations.Singular.unit S) ≠
      (2 : ℚ) • localTraceCap S 0 2 c (HodgeLean.Foundations.Singular.unit S) := by
  rw [unit_cap]
  exact (double_ne c_ne).symm

example := cap_naturality_falsification

#print axioms exists_falsification
#print axioms uniqueness_falsification
#print axioms cap_falsification
#print axioms homeomorph_falsification
#print axioms cap_naturality_falsification
end HodgeLean.Foundations.RationalHomologyManifold.Checks

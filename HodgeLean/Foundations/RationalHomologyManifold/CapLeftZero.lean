import HodgeLean.Foundations.RationalHomologyManifold.TopClass
import HodgeLean.Foundations.RationalHomologyManifold.CapNaturality
import HodgeLean.Foundations.QuotientDuality.LocalTriangulationConnectedness

/-! The complementary-degree edge with degree-zero source cohomology.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Cap with the singular cup unit returns the original homology class.
Source: Hatcher, Algebraic Topology, section 3.3, cup-cap evaluation and the cup unit.
HC no distance; AV milestone no distance.
-/
theorem cap_left_unit (X : TopCat.{0}) (q : ℕ) (c : Homology ℚ X (0 + q)) :
    localTraceCap X 0 q c (HodgeLean.Foundations.Singular.unit X) =
      (by simpa only [Nat.zero_add] using c) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  obtain ⟨b, rfl⟩ := (cohomologyEquivDualHomology ℚ X q).surjective l
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [cap_evaluation]
  have ht (k : ℕ) (h : 0 + q = k) :
      cohomologyEquivDualHomology ℚ X (0 + q)
        (HodgeLean.Foundations.Singular.cup X rfl
          (HodgeLean.Foundations.Singular.unit X) b) c =
      cohomologyEquivDualHomology ℚ X k
        (HodgeLean.Foundations.Singular.cup X h
          (HodgeLean.Foundations.Singular.unit X) b)
        (cast (congrArg (fun j => ↥(Homology ℚ X j)) h) c) := by
    cases h
    rfl
  rw [ht q (Nat.zero_add q), HodgeLean.Foundations.Singular.one_cup]
  rfl


#print axioms cap_left_unit
/-- Cap maps degree-zero cohomology bijectively to top homology.
Source: Hatcher, Algebraic Topology, section 3.3, the cap unit and Theorem 3.26.
HC no distance; AV milestone no distance.
-/
theorem cap_left_zero_bijective (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X) (q : ℕ)
    (o : LocalRationalOrientation X (0 + q)) (c : Homology ℚ X (0 + q))
    (hc : localization X (0 + q) c = o.generator) :
    Function.Bijective (localTraceCap X 0 q c) := by
  letI := triangulated_pathConnected X t.ambient t.complex t.finite_faces t.realization
  let c' : Homology ℚ X q := by simpa only [Nat.zero_add] using c
  have ht (m : ℕ) (h : 0 + q = m) :
      let c' := cast (congrArg (fun j => ↥(Homology ℚ X j)) h) c
      c' ≠ 0 ∧ ∀ z : Homology ℚ X m, ∃ r : ℚ, r • c' = z := by
    cases h
    exact ⟨global_class_ne_zero_of_local_generators X (0 + q) o c
      (fun x => congrFun hc x), topClass_spans X t (0 + q) o c hc⟩
  obtain ⟨hc0, hspan⟩ := ht q (Nat.zero_add q)
  change c' ≠ 0 at hc0
  change ∀ z : Homology ℚ X q, ∃ r : ℚ, r • c' = z at hspan
  have hu : localTraceCap X 0 q c (HodgeLean.Foundations.Singular.unit X) = c' :=
    cap_left_unit X q c
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hc0
  constructor
  · intro a b hab
    obtain ⟨r, rfl⟩ := exists_smul_singular_unit X a
    obtain ⟨s, rfl⟩ := exists_smul_singular_unit X b
    have hrs : r = s := by
      have hh := congrArg f hab
      simpa only [map_smul, hu, hf, smul_eq_mul, mul_one] using hh
    rw [hrs]
  · intro z
    obtain ⟨r, hr⟩ := hspan z
    refine ⟨r • HodgeLean.Foundations.Singular.unit X, ?_⟩
    rw [map_smul, hu, hr]

#print axioms cap_left_zero_bijective
end HodgeLean.Foundations.RationalHomologyManifold

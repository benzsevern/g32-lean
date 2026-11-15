import HodgeLean.Foundations.RationalHomologyManifold.GlobalDetection
import HodgeLean.Foundations.RationalHomologyManifold.LocalCoefficients
import HodgeLean.Foundations.QuotientDuality.LocalZeroDuality

/-! Scalar coordinates on top homology and evaluation against its normalized class.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every top class is a scalar multiple of a normalized class on a connected finite polyhedron.
Source: Hatcher, Algebraic Topology, Theorem 3.26; Bredon, Sheaf Theory, second edition, V.16.
HC no distance; AV milestone no distance.
-/
theorem topClass_spans (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X) (n : ℕ)
    (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : localization X n c = o.generator) (z : Homology ℚ X n) :
    ∃ r : ℚ, r • c = z := by
  let x : X := Classical.choice inferInstance
  obtain ⟨r, hr⟩ := (o.generates x).2 (localization X n z x)
  refine ⟨r, finiteTriangulation_localization_injective X t n o ?_⟩
  apply localization_eq_of_eq_at_point X n o (r • c) z x
  rw [show localization X n (r • c) x = r • localization X n c x from
    congrFun (map_smul (localization X n) r c) x, congrFun hc x]
  exact hr

#print axioms topClass_spans
/-- Evaluation on the normalized class gives scalar coordinates on top cohomology.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and the rational universal coefficient theorem.
HC no distance; AV milestone no distance.
-/
theorem topClass_evaluation_bijective (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X) (n : ℕ)
    (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : localization X n c = o.generator) :
    Function.Bijective (fun a : Cohomology ℚ X n =>
      cohomologyEquivDualHomology ℚ X n a c) := by
  constructor
  · intro a b hab
    change cohomologyEquivDualHomology ℚ X n a c =
      cohomologyEquivDualHomology ℚ X n b c at hab
    apply (cohomologyEquivDualHomology ℚ X n).injective
    ext z
    obtain ⟨r, rfl⟩ := topClass_spans X t n o c hc z
    rw [map_smul, map_smul, hab]
  · intro r
    have hc0 := global_class_ne_zero_of_local_generators X n o c
      (fun x => congrFun hc x)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hc0
    refine ⟨r • (cohomologyEquivDualHomology ℚ X n).symm f, ?_⟩
    change cohomologyEquivDualHomology ℚ X n
      (r • (cohomologyEquivDualHomology ℚ X n).symm f) c = r
    rw [map_smul, LinearMap.smul_apply, LinearEquiv.apply_symm_apply, hf]
    exact mul_one r

#print axioms topClass_evaluation_bijective
end HodgeLean.Foundations.RationalHomologyManifold

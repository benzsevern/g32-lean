import HodgeLean.Foundations.QuotientDuality.LocalAbsoluteCompactLift
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.CompactModel
import HodgeLean.Foundations.RationalHomologyManifold.OpenHomologyBound

/-! A uniform singular homology bound for open subsets of real polynomial carriers. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.ComplexTopology HodgeLean.Foundations.RationalHomologyManifold
namespace HodgeLean.Foundations.QuotientDuality

theorem polynomial_carrier_open_homology_bound {n m : ℕ}
    (a b : Fin m → MvPolynomial (Fin n) ℝ) (U : TopCat.{0})
    (j : U ⟶ TopCat.of (realPolynomialCarrier a b)) (hj : IsOpenEmbedding j)
    (i : ℕ) (hi : n < i) : Subsingleton (Homology ℚ U i) := by
  classical
  apply subsingleton_of_forall_eq 0
  intro c
  obtain ⟨K, hK, d, hd⟩ := absolute_homology_compact_lift U i c
  let f : K → EuclideanSpace ℝ (Fin n) := fun x => (j x.val).val
  have hf : Continuous f := continuous_subtype_val.comp (hj.continuous.comp continuous_subtype_val)
  have hS := hK.image (continuous_subtype_val.comp hj.continuous)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).mp hS.isBounded
  let R := max r 0
  let T := realPolynomialCarrier a b ∩ Metric.closedBall 0 R
  let Y := TopCat.of T
  obtain ⟨L, hL, ⟨eL⟩⟩ := polynomial_truncation_triangulation a b 0 (le_max_right r 0)
  let t : FiniteTriangulation Y := ⟨n, L, hL, eL.symm⟩
  let p : Y → realPolynomialCarrier a b := fun y => ⟨y.val, y.property.1⟩
  have hp : Continuous p := continuous_subtype_val.subtype_mk _
  let V : Opens Y := ⟨p ⁻¹' Set.range j, hj.isOpen_range.preimage hp⟩
  let e := hj.toIsEmbedding.toHomeomorph
  let l : V → U := fun v => e.symm ⟨p v.val, v.property⟩
  have hl : Continuous l := e.symm.continuous.comp ((hp.comp continuous_subtype_val).subtype_mk _)
  have hball (x : K) : (j x.val).val ∈ Metric.closedBall 0 R :=
    (Metric.closedBall_subset_closedBall (le_max_left r 0)) (hr ⟨x.val, x.property, rfl⟩)
  let k : K → V := fun x =>
    ⟨⟨(j x.val).val, ⟨(j x.val).property, hball x⟩⟩, ⟨x.val, rfl⟩⟩
  have hk : Continuous k := (hf.subtype_mk _).subtype_mk _
  let km : TopCat.of K ⟶ TopCat.of V := TopCat.ofHom ⟨k, hk⟩
  let lm : TopCat.of V ⟶ U := TopCat.ofHom ⟨l, hl⟩
  have hkl : km ≫ lm = (TopPair.ofSubset (X := U) K).map := by
    ext x
    apply e.injective
    exact e.apply_symm_apply ⟨j x.val, ⟨x.val, rfl⟩⟩
  have hV : Subsingleton (Homology ℚ (TopCat.of V) i) :=
    finiteTriangulation_open_homology_bound Y t (TopCat.of V)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
      V.isOpen.isOpenEmbedding_subtypeVal i hi
  have hzero : homologyMap ℚ i km d = 0 := @Subsingleton.elim _ hV _ _
  rw [← hd, ← hkl, homologyMap_comp, LinearMap.comp_apply]
  exact (congrArg (homologyMap ℚ i lm) hzero).trans (map_zero _)

#print axioms polynomial_carrier_open_homology_bound
end HodgeLean.Foundations.QuotientDuality

import HodgeLean.Foundations.Program.SchoenTransferE1Defs
import HodgeLean.RealDefs.TopDegreeRank

/-! Curve cohomology action infrastructure for the ordered tensor comparison. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

/-- Every endomorphism fixes degree-zero cohomology of a connected variety.
Source: Hatcher, Algebraic Topology, §3.1, degree-zero cohomology and functoriality. -/
theorem s4_e1_degree_zero_action
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (δ : Y ⟶ Y) : homPullback δ 0 = LinearMap.id := by
  letI := pathConnectedSpace_complexPoint Y
  have hr : Module.rank ℚ (HQ Y 0) ≤ 1 := rank_H0_le_one Y
  have hs : Submodule.span ℚ {cupUnit Y} = ⊤ :=
    span_singleton_eq_top_of_rank_le_one hr (unitClass_ne_zero' Y)
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℚ {cupUnit Y} := by rw [hs]; trivial
  obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, spec_homPullback_unit, LinearMap.id_apply]

/-- Cohomology of a smooth projective curve vanishes above degree two.
Source: Hatcher, Algebraic Topology, Lemma 3.27 and Theorem 3.26; `j5d_subsingleton_HQ_of_lt`. -/
theorem s4_e1_curve_cohomology_vanishing
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) {n : ℕ} (hn : 2 < n) :
    Subsingleton (HQ Y n) := by
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    rw [← hdim]
    infer_instance
  exact j5d_subsingleton_HQ_of_lt Y 1 hn

/-- A nontrivial primitive character is absent from an identity representation.
Source: Schoen (1988), Lemma 1.1; coprimality of rational cyclotomic polynomials. -/
theorem s4_e1_identity_primitive_kernel
    (V : Type*) [AddCommGroup V] [Module ℚ V] (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.ker (Polynomial.aeval (LinearMap.id : Module.End ℚ V)
      (Polynomial.cyclotomic m ℚ)) = ⊥ := by
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime (LinearMap.id : Module.End ℚ V)
    (Polynomial.cyclotomic.isCoprime_rat (show m ≠ 1 by omega))
  simpa only [Polynomial.cyclotomic_one, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_one, Module.End.one_eq_id, sub_self, LinearMap.ker_zero,
    disjoint_top] using hd

#print axioms s4_e1_degree_zero_action
#print axioms s4_e1_curve_cohomology_vanishing
#print axioms s4_e1_identity_primitive_kernel

end HodgeLean.Foundations.Program

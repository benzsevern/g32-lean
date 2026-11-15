import HodgeLean.Foundations.Abdulali.RationalCurveNumerator
import HodgeLean.Foundations.MatrixAlgGroupLieIdentityComponent
import Mathlib.Topology.Irreducible
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations MvPolynomial

/-- Matrix curves with rational coordinates are Zariski continuous on their
pole-free parameters, equipped with the cofinite topology.
Source: Borel, Linear Algebraic Groups, second edition, AG.1, regular maps
on principal affine open subsets. -/
theorem rational_matrix_curve_continuous
    {K D : Type*} [Field K] {n : ℕ}
    (v : D → K) (hv : Function.Injective v) (q : Polynomial K)
    (hq : ∀ d, q.eval (v d) ≠ 0)
    (c : D → Matrix.GeneralLinearGroup (Fin n) K)
    (p : Fin n × Fin n → Polynomial K)
    (hp : ∀ d ij, g1_coords (c d) ij = (p ij).eval (v d) / q.eval (v d)) :
    @Continuous (CofiniteTopology D) _ inferInstance (g1_zariski K n)
      (fun d => c (((CofiniteTopology.of : D ≃ CofiniteTopology D)).symm d)) := by
  letI := g1_zariski K n
  let e := (CofiniteTopology.of : D ≃ CofiniteTopology D).symm
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨s, rfl⟩ := (g1_isClosed_iff Z).mp hZ
  have heq : (fun d : CofiniteTopology D => c (e d)) ⁻¹' g1_zeroSet s =
      ⋂ f ∈ s, {d | eval (fun ij => (p ij).eval (v (e d)) / q.eval (v (e d))) f = 0} := by
    ext d
    have hc : g1_coords (c (e d)) =
        (fun ij => (p ij).eval (v (e d)) / q.eval (v (e d))) := funext (hp (e d))
    simp only [Set.mem_preimage, g1_zeroSet, Set.mem_setOf_eq, Set.mem_iInter, hc]
  change IsClosed ((fun d : CofiniteTopology D => c (e d)) ⁻¹' g1_zeroSet s)
  rw [heq]
  refine isClosed_biInter fun f _ => ?_
  obtain ⟨N, P, hP⟩ := polynomial_eval_div_numerator p q f
  have hz : {d : CofiniteTopology D |
        eval (fun ij => (p ij).eval (v (e d)) / q.eval (v (e d))) f = 0} =
      {d | P.eval (v (e d)) = 0} := by
    ext d
    simp only [Set.mem_setOf_eq, hP _ (hq _),
      div_eq_zero_iff, pow_ne_zero N (hq _), or_false]
  rw [hz]
  apply CofiniteTopology.isClosed_iff.mpr
  by_cases h : P = 0
  · left
    ext d
    simp only [Set.mem_setOf_eq, h, Polynomial.eval_zero, Set.mem_univ]
  · right
    exact (Polynomial.finite_setOfPred_isRoot h).preimage (hv.comp e.injective).injOn

/-- A rational matrix curve through the identity stays in the identity
component of any matrix algebraic group containing the curve.
Source: Borel, Linear Algebraic Groups, second edition, II.7. -/
theorem rational_matrix_curve_mem_component
    {K D : Type*} [Field K] [Infinite D] {n : ℕ}
    (G : HodgeLean.Foundations.Program.MatrixAlgGroup K n)
    (v : D → K) (hv : Function.Injective v) (q : Polynomial K)
    (hq : ∀ d, q.eval (v d) ≠ 0)
    (c : D → Matrix.GeneralLinearGroup (Fin n) K)
    (p : Fin n × Fin n → Polynomial K)
    (hp : ∀ d ij, g1_coords (c d) ij = (p ij).eval (v d) / q.eval (v d))
    (hG : ∀ d, c d ∈ G.carrier) (d₀ d : D) (h₀ : c d₀ = 1) :
    c d ∈ g1_identityComponent G := by
  letI := g1_zariski K n
  have hc := rational_matrix_curve_continuous v hv q hq c p hp
  have hconn := isConnected_range hc
  exact hconn.isPreconnected.subset_connectedComponentIn
    ⟨(CofiniteTopology.of : D ≃ CofiniteTopology D) d₀, h₀⟩
    (by rintro _ ⟨x, rfl⟩; exact hG _) ⟨(CofiniteTopology.of : D ≃ CofiniteTopology D) d, rfl⟩

#print axioms rational_matrix_curve_continuous
#print axioms rational_matrix_curve_mem_component
end HodgeLean.Foundations.Abdulali

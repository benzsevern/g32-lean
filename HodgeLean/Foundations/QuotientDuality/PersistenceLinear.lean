import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Projection
import Mathlib.FieldTheory.Separable

/-! Linear lifting for finite-order actions. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

open Module Polynomial

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

lemma persistence_finite_order_semisimple [CharZero K]
    (T : Module.End K U) (m : ℕ) (hm : 0 < m) (hT : T ^ m = 1) :
    T.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((Polynomial.separable_X_pow_sub_C (1 : K)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)) one_ne_zero).squarefree)
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    map_one, hT, sub_self]

lemma persistence_semisimple_eigen_lift
    (T : Module.End K U) (S : Module.End K V) (f : U →ₗ[K] V)
    (hf : ∀ x, f (T x) = S (f x)) (hT : T.IsSemisimple)
    (ζ : K) (v : V) (hv : S v = ζ • v) (hvr : v ∈ LinearMap.range f) :
    ∃ u : U, T u = ζ • u ∧ f u = v := by
  have hk : LinearMap.ker f ∈ T.invtSubmodule := by
    intro x hx
    change f (T x) = 0
    rw [hf, LinearMap.mem_ker.mp hx, map_zero]
  obtain ⟨Q, hQ, hc⟩ := (Module.End.isSemisimple_iff).mp hT _ hk
  obtain ⟨x, hx⟩ := hvr
  let e := Submodule.prodEquivOfIsCompl (LinearMap.ker f) Q hc
  let u : Q := (e.symm x).2
  have hxu : f (u : U) = v := by
    have he := e.apply_symm_apply x
    change ((e.symm x).1 : U) + (u : U) = x at he
    have hh := congrArg f he
    rw [map_add, LinearMap.mem_ker.mp (e.symm x).1.property, zero_add] at hh
    exact hh.trans hx
  refine ⟨u, ?_, hxu⟩
  have hker : T (u : U) - ζ • (u : U) ∈ LinearMap.ker f := by
    change f _ = 0
    rw [map_sub, map_smul, hf, hxu, hv, sub_self]
  have hq : T (u : U) - ζ • (u : U) ∈ Q :=
    Q.sub_mem (hQ u.property) (Q.smul_mem ζ u.property)
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hc.disjoint) _ hker hq)

end HodgeLean.Foundations.QuotientDuality

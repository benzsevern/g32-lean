import Mathlib.RingTheory.Invariant.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Scalar-preserving evaluations into the scalar field are determined by their kernels. -/
theorem evaluation_eq_of_kernel_eq
    {k B : Type*} [Field k] [CommRing B] [Algebra k B]
    (p q : B →ₐ[k] k) (h : RingHom.ker p.toRingHom = RingHom.ker q.toRingHom) :
    p = q := by
  apply AlgHom.ext
  intro b
  have hb : b - algebraMap k B (q b) ∈ RingHom.ker q.toRingHom := by
    change q (b - algebraMap k B (q b)) = 0
    rw [map_sub, q.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [← h] at hb
  change p (b - algebraMap k B (q b)) = 0 at hb
  rw [map_sub, p.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at hb
  exact hb

/-- Evaluations over the same invariant-base point form a single finite-group orbit. -/
theorem invariant_evaluation_orbit
    {k R B G : Type*} [Field k] [CommRing R] [CommRing B]
    [Algebra k B] [Algebra R B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G R B] [SMulCommClass G k B]
    [Algebra.IsInvariant R B G]
    (p q : B →ₐ[k] k)
    (hbase : ∀ r, p (algebraMap R B r) = q (algebraMap R B r)) :
    ∃ g : G, ∀ b, p (g • b) = q b := by
  have hker : (RingHom.ker p.toRingHom).under R = (RingHom.ker q.toRingHom).under R := by
    ext r
    change p (algebraMap R B r) = 0 ↔ q (algebraMap R B r) = 0
    rw [hbase]
  haveI : (RingHom.ker p.toRingHom).IsPrime := RingHom.ker_isPrime p.toRingHom
  haveI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime q.toRingHom
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R B G
    (RingHom.ker p.toRingHom) (RingHom.ker q.toRingHom) hker
  let r : B →ₐ[k] k := p.comp (MulSemiringAction.toAlgEquiv k B g⁻¹).toAlgHom
  have hr : RingHom.ker r.toRingHom = RingHom.ker q.toRingHom := by
    rw [hg]
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have he : r = q := evaluation_eq_of_kernel_eq r q hr
  refine ⟨g⁻¹, ?_⟩
  intro b
  exact AlgHom.congr_fun he b

end AlgebraicGeometry.RamifiedNormalization.StageFour

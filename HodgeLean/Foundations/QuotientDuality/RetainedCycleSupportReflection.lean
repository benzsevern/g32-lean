import HodgeLean.Foundations.QuotientDuality.RetainedCycleIsomorphismOpen

noncomputable section
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_closure_reflection_on_isomorphism_open {X Y : Scheme.{0}}
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] (ξ x : X) (hx : f x ∈ U) :
    x ∈ closure ({ξ} : Set X) ↔ f x ∈ closure ({f ξ} : Set Y) := by
  constructor
  · intro h
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr h).map f.continuous)
  · intro h
    have hsp : f ξ ⤳ f x := specializes_iff_mem_closure.mpr h
    have hξ : f ξ ∈ U := hsp.mem_open U.isOpen hx
    let ξU : (f ⁻¹ᵁ U).toScheme := ⟨ξ, hξ⟩
    let xU : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
    have ht : (f ∣_ U) ξU ⤳ (f ∣_ U) xU := by
      apply U.ι.isOpenEmbedding.isInducing.specializes_iff.mp
      simpa only [Scheme.Opens.ι_apply, morphismRestrict_base_coe] using hsp
    have hs : ξU ⤳ xU := (f ∣_ U).isOpenEmbedding.isInducing.specializes_iff.mp ht
    exact specializes_iff_mem_closure.mp (hs.map (f ⁻¹ᵁ U).ι.continuous)


theorem retained_prime_support_iff (X : Over (Spec ↧ℂ))
    (ξ : X.left) (z : ComplexPoint X) :
    z ∈ a3b4_cycleSupport X.hom (properPrime ξ) ↔
      z.underlying ∈ closure ({ξ} : Set X.left) := by
  simp only [a3b4_cycleSupport, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    have he : y = ξ := by
      by_contra h
      exact hy (by simp only [properPrime, Function.locallyFinsuppWithin.single_apply,
        ite_eq_right h])
    simpa only [he] using hz
  · intro hz
    refine ⟨ξ, ?_, hz⟩
    change properPrime ξ ξ ≠ 0
    simp only [properPrime, Function.locallyFinsuppWithin.single_apply, ite_true,
      ne_eq, one_ne_zero, not_false_eq_true]

theorem retained_prime_support_reflection {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (U : Y.left.Opens) [IsIso (f.left ∣_ U)]
    (ξ : X.left) (z : ComplexPoint X) (hz : (Point.map f z).underlying ∈ U) :
    z ∈ a3b4_cycleSupport X.hom (properPrime ξ) ↔
      Point.map f z ∈ a3b4_cycleSupport Y.hom (properPrime (f.left ξ)) := by
  rw [retained_prime_support_iff, retained_prime_support_iff, Point.underlying_map]
  exact retained_closure_reflection_on_isomorphism_open f.left U ξ z.underlying hz

end HodgeLean.Foundations.QuotientDuality

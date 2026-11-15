import HodgeLean.Foundations.Program.SchoenCycleC2LinearHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Disjoint component ranges give distinct component generic points. -/
theorem s2e_orbit_generic_injective
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left)) :
    Function.Injective (fun t : Fin m =>
      (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) := by
  intro s t hst
  by_contra hne
  exact Set.disjoint_left.mp (hdisj s t hne)
    ⟨genericPoint Q.left, rfl⟩ ⟨genericPoint Q.left, hst.symm⟩

/-- The coefficient at each actual component generic point is the specified rational weight. -/
theorem s2e_rationalOrbitCycle_apply_generic
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ)
    (hi : Function.Injective (fun t : Fin m =>
      (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)))
    (a : Fin m → ℚ) (t : Fin m) :
    s2e_rationalOrbitCycle ι δ m a
      ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) = a t := by
  classical
  simp only [s2e_rationalOrbitCycle, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, Function.locallyFinsuppWithin.mapRange_apply,
    s2e_componentCycle, Function.locallyFinsuppWithin.single_apply,
    hi.eq_iff]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- Rational orbit support retains exactly the components with nonzero coefficient. -/
theorem s2e_rationalOrbitCycle_support_eq
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ)
    (hi : Function.Injective (fun t : Fin m =>
      (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left))) (a : Fin m → ℚ) :
    (s2e_rationalOrbitCycle ι δ m a).support =
      ⋃ t : Fin m, ⋃ (_ : a t ≠ 0),
        {(ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp
      (s2e_rationalOrbitCycle_support_subset ι δ m a hx)
    rw [s2e_componentCycle_support] at ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨?_, Set.mem_singleton _⟩⟩
    simpa only [Function.mem_support, s2e_rationalOrbitCycle_apply_generic ι δ m hi] using hx
  · intro hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ha, hx⟩ := Set.mem_iUnion.mp ht
    obtain rfl := Set.mem_singleton_iff.mp hx
    change s2e_rationalOrbitCycle ι δ m a _ ≠ 0
    rw [s2e_rationalOrbitCycle_apply_generic ι δ m hi]
    exact ha

/-- The analytic support is the union of precisely the nonzero weighted component ranges. -/
theorem s2e_rationalOrbitCycle_analytic_support_eq
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ)
    (hi : Function.Injective (fun t : Fin m =>
      (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)))
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (a : Fin m → ℚ) :
    a3b4_cycleSupport W.hom (s2e_rationalOrbitCycle ι δ m a) =
      Point.underlying ⁻¹' ⋃ t : Fin m, ⋃ (_ : a t ≠ 0),
        Set.range (ι ≫ (End.of δ ^ t.val).asHom).left := by
  ext x
  change (x.underlying ∈ ⋃ ξ ∈ (s2e_rationalOrbitCycle ι δ m a).support, closure {ξ}) ↔ _
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hx
    rw [s2e_rationalOrbitCycle_support_eq ι δ m hi a] at hξ
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hξ
    obtain ⟨ha, hξ⟩ := Set.mem_iUnion.mp ht
    obtain rfl := Set.mem_singleton_iff.mp hξ
    let : IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left := himm t
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ha, ?_⟩⟩
    simpa only [s2e_componentCycle_closure] using hxξ
  · intro hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ha, ht⟩ := Set.mem_iUnion.mp ht
    let : IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left := himm t
    refine Set.mem_iUnion₂.mpr ⟨(ι ≫ (End.of δ ^ t.val).asHom).left
      (genericPoint Q.left), ?_, ?_⟩
    · rw [s2e_rationalOrbitCycle_support_eq ι δ m hi a]
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ha, Set.mem_singleton _⟩⟩
    · simpa only [s2e_componentCycle_closure] using ht

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleC2OrbitSupportHelpers
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- At any point of the component, its frozen multiplicity is one. -/
theorem s2e_componentCycle_multiplicity
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [QuasiCompact W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (x : ComplexPoint W) (hx : x.underlying ∈ Set.range ι.left) :
    a3b4_multiplicity W.hom (s2e_componentCycle ι ℚ) x = 1 := by
  have hξ : ι.left (genericPoint Q.left) ∈ (s2e_componentCycle ι ℚ).support := by
    rw [s2e_componentCycle_support]
    exact Set.mem_singleton _
  have heq := a3b4a_classMultiplicity_eq_component W.hom (s2e_componentCycle ι ℚ)
    (ι.left (genericPoint Q.left)) hξ x
    (by simpa only [s2e_componentCycle_closure] using hx)
    (by
      intro η hη hne
      rw [s2e_componentCycle_support] at hη
      exact (hne (Set.mem_singleton_iff.mp hη)).elim)
  simpa only [s2e_componentCycle, Function.locallyFinsuppWithin.single_apply,
    ite_true] using heq

/-- On a nonzero weighted orbit component the frozen multiplicity is its exact weight. -/
theorem s2e_rationalOrbitCycle_multiplicity
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [QuasiCompact W.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ)
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left))
    (a : Fin m → ℚ) (t : Fin m) (ha : a t ≠ 0)
    (x : ComplexPoint W)
    (hx : x.underlying ∈ Set.range (ι ≫ (End.of δ ^ t.val).asHom).left) :
    a3b4_multiplicity W.hom (s2e_rationalOrbitCycle ι δ m a) x = a t := by
  have hi := s2e_orbit_generic_injective ι δ m hdisj
  let ξ := (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)
  have hξ : ξ ∈ (s2e_rationalOrbitCycle ι δ m a).support := by
    change s2e_rationalOrbitCycle ι δ m a ξ ≠ 0
    exact (s2e_rationalOrbitCycle_apply_generic ι δ m hi a t).trans_ne ha
  let : IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left := himm t
  have hxξ : x.underlying ∈ closure ({ξ} : Set W.left) := by
    simpa only [ξ, s2e_componentCycle_closure] using hx
  have hother : ∀ η ∈ (s2e_rationalOrbitCycle ι δ m a).support,
      η ≠ ξ → x.underlying ∉ closure ({η} : Set W.left) := by
    intro η hη hne hxη
    rw [s2e_rationalOrbitCycle_support_eq ι δ m hi a] at hη
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hη
    obtain ⟨_, hs⟩ := Set.mem_iUnion.mp hs
    obtain rfl := Set.mem_singleton_iff.mp hs
    have hst : s ≠ t := by
      intro h
      subst s
      exact hne rfl
    let : IsClosedImmersion (ι ≫ (End.of δ ^ s.val).asHom).left := himm s
    rw [s2e_componentCycle_closure] at hxη
    exact Set.disjoint_left.mp (hdisj s t hst) hxη hx
  rw [a3b4a_classMultiplicity_eq_component W.hom _ ξ hξ x hxξ hother]
  exact s2e_rationalOrbitCycle_apply_generic ι δ m hi a t

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.GaloisEvaluationOrbits
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original full-order field symmetry generates every integral evaluation fibre orbit. -/
theorem integralClosure_evaluation_deck_orbit
    {k R K L : Type*} [Field k] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra k R] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (δ : L ≃ₐ[K] L) (hδ : orderOf δ = Module.finrank K L)
    (p q : integralClosure R L →+* k)
    (hbase : ∀ r, p (algebraMap R (integralClosure R L) r) =
      q (algebraMap R (integralClosure R L) r))
    (hp : ∀ a : k, p (algebraMap R (integralClosure R L) (algebraMap k R a)) = a)
    (hq : ∀ a : k, q (algebraMap R (integralClosure R L) (algebraMap k R a)) = a) :
    letI := IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
    ∃ n : ℕ, ∀ b, p (δ ^ n • b) = q b := by
  letI := IsIntegralClosure.MulSemiringAction R K L (integralClosure R L)
  obtain ⟨g, hg⟩ := integralClosure_evaluation_orbit (K := K) p q hbase hp hq
  have hcard : Nat.card (Subgroup.zpowers δ) = Nat.card (L ≃ₐ[K] L) := by
    rw [Nat.card_zpowers, hδ, IsGalois.card_aut_eq_finrank]
  have hgen : Subgroup.zpowers δ = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp hcard
  have hgmem : g ∈ Submonoid.powers δ :=
    (isOfFinOrder_of_finite δ).mem_powers_iff_mem_zpowers.mpr (by rw [hgen]; trivial)
  obtain ⟨n, hn⟩ := hgmem
  dsimp only at hn
  exact ⟨n, fun b => by rw [hn]; exact hg b⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour

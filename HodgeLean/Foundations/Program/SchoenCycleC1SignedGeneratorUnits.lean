import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Changing generators of the same principal branch ideals changes a
signed rational coefficient product by one actual section unit. -/
theorem s2e_c1_signed_generator_unit
    {R K J : Type*} [CommRing R] [IsDomain R] [Field K] [Fintype J]
    (φ : R →+* K) (g h : J → R) (n : J → ℤ)
    (hI : ∀ j, Ideal.span {g j} = Ideal.span {h j}) :
    ∃ u : Rˣ, (∏ j, (φ (g j)) ^ n j) = φ (u : R) * ∏ j, (φ (h j)) ^ n j := by
  classical
  have hunit (j : J) : ∃ v : Rˣ, g j = (v : R) * h j := by
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp (hI j).symm
    exact ⟨v, hv.symm.trans (mul_comm _ _)⟩
  choose v hv using hunit
  let u : Rˣ := ∏ j, v j ^ n j
  have hu : φ (u : R) = ∏ j, (φ (v j : R)) ^ n j := by
    change ((Units.map φ.toMonoidHom (∏ j, v j ^ n j) : Kˣ) : K) = _
    change (Units.coeHom K) ((Units.map φ.toMonoidHom) (∏ j, v j ^ n j)) = _
    rw [map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [map_zpow]
    change (((Units.map φ.toMonoidHom (v j)) ^ n j : Kˣ) : K) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  refine ⟨u, ?_⟩
  simp_rw [hv, map_mul, mul_zpow]
  rw [Finset.prod_mul_distrib, hu]

end HodgeLean.Foundations.Program

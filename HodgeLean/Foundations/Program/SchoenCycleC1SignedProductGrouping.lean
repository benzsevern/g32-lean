import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Grouping repeated parameters into marked branch products retains an
actual residual unit for every signed order. -/
theorem s2e_c1_signed_product_grouping
    {R K I J : Type*} [CommRing R] [Field K] [Fintype I] [Fintype J] [DecidableEq J]
    (φ : R →+* K) (g : I → J) (t : I → R) (b : J → R) (v : J → Rˣ)
    (hb : ∀ j, b j = (∏ i ∈ Finset.univ.filter (fun i => g i = j), t i) * (v j : R))
    (n : J → ℤ) (u : Rˣ) :
    ∃ w : Rˣ, φ (u : R) * ∏ i, (φ (t i)) ^ n (g i) =
      φ (w : R) * ∏ j, (φ (b j)) ^ n j := by
  let ψ : Rˣ →* K := φ.toMonoidHom.comp (Units.coeHom R)
  let V : Rˣ := ∏ j, v j ^ n j
  have hterm (j : J) : (φ (b j)) ^ n j =
      (∏ i ∈ Finset.univ.filter (fun i => g i = j), (φ (t i)) ^ n (g i)) * ψ (v j ^ n j) := by
    rw [hb, map_mul, mul_zpow, map_prod, ← Finset.prod_zpow, map_zpow]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hprod : (∏ j, (φ (b j)) ^ n j) = (∏ i, (φ (t i)) ^ n (g i)) * ψ V := by
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_fiberwise]
    congr 1
    exact (map_prod ψ (fun j => v j ^ n j) Finset.univ).symm
  refine ⟨u * V⁻¹, ?_⟩
  rw [hprod]
  change ψ u * _ = ψ (u * V⁻¹) * _
  rw [map_mul, map_inv]
  have hV : ψ V ≠ 0 := (Units.map φ.toMonoidHom V).ne_zero
  calc
    ψ u * (∏ i, (φ (t i)) ^ n (g i)) =
        ψ u * (∏ i, (φ (t i)) ^ n (g i)) * ((ψ V)⁻¹ * ψ V) := by
          rw [inv_mul_cancel₀ hV, mul_one]
    _ = (ψ u * (ψ V)⁻¹) * ((∏ i, (φ (t i)) ^ n (g i)) * ψ V) := by ring

end HodgeLean.Foundations.Program

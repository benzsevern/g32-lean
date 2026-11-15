import HodgeLean.Foundations.QuotientDuality.MonomialSignedProductFactorization
import HodgeLean.Foundations.QuotientDuality.MonomialBaseFieldRescaling

/-! Reduction of an actual Kummer generator to nonnegative branch residue weights. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem signed_kummer_generator_residue_reduction
    {R K J : Type*} [CommRing R] [Field K] [Algebra R K] [Fintype J]
    (hinj : Function.Injective (algebraMap R K))
    (m : ℕ) (hm : 0 < m) (g : J → R) (hg : ∀ j, g j ≠ 0)
    (a : J → ℤ) (u : Rˣ) (v : K)
    (hv : v ^ m = algebraMap R K (u : R) * ∏ j, (algebraMap R K (g j)) ^ a j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤) :
    ∃ w : K,
      w ^ m = algebraMap R K (u : R) *
        ∏ j, (algebraMap R K (g j)) ^ (a j % (m : ℤ)).toNat ∧
      Subfield.closure (Set.range (algebraMap R K) ∪ {w}) = ⊤ := by
  let G : J → K := fun j => algebraMap R K (g j)
  have hG (j : J) : G j ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hg j)
  let e : K := ∏ j, G j ^ (a j / (m : ℤ))
  have he : e ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hG j)
  let F := Subfield.closure (Set.range (algebraMap R K))
  have heF : e ∈ F := by
    apply F.prod_mem
    intro j _
    exact F.zpow_mem (Subfield.subset_closure ⟨g j, rfl⟩) _
  have hprod := signed_branch_product_residue_factorization m hm G hG a
  refine ⟨v / e, ?_, field_generator_div_base_closure _ v e heF he hgen⟩
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero m he)).mpr
  rw [hv]
  change algebraMap R K (u : R) * (∏ j, G j ^ a j) = _
  rw [hprod]
  ac_rfl

#print axioms signed_kummer_generator_residue_reduction
end HodgeLean.Foundations.QuotientDuality

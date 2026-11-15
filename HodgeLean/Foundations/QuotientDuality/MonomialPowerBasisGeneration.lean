import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Field.Subfield.Basic

/-! Field generation by an actual power-basis generator and the affine coefficient ring. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

theorem powerBasis_field_closure_eq_top
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra F K] [Algebra R K]
    [IsScalarTower R F K] (P : PowerBasis F K) :
    Subfield.closure (Set.range (algebraMap R K) ∪ {P.gen}) = ⊤ := by
  let T := Subfield.closure (Set.range (algebraMap R K) ∪ {P.gen})
  have hcoeff (x : F) : algebraMap F K x ∈ T := by
    obtain ⟨a, b, _, he⟩ := IsFractionRing.div_surjective R x
    rw [← he, map_div₀, ← IsScalarTower.algebraMap_apply R F K,
      ← IsScalarTower.algebraMap_apply R F K]
    exact T.div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  let A : Subalgebra F K := { T.toSubring with algebraMap_mem' := hcoeff }
  have hle : Algebra.adjoin F ({P.gen} : Set K) ≤ A := by
    apply Algebra.adjoin_le_iff.mpr
    rintro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact Subfield.subset_closure (Or.inr rfl)
  rw [P.adjoin_gen_eq_top] at hle
  apply top_unique
  intro x _
  exact hle (show x ∈ (⊤ : Subalgebra F K) from trivial)

#print axioms powerBasis_field_closure_eq_top
end HodgeLean.Foundations.QuotientDuality

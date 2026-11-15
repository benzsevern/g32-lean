import HodgeLean.Blocks.Weil.RationalKernel

/-! # The exterior-power quotient under scalar restriction -/

noncomputable section

set_option maxHeartbeats 400000

namespace HodgeBlocks.ExteriorRestriction

variable {K V : Type*} [Field K] [Algebra ℚ K] [AddCommGroup V]
  [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]

/-- Restriction of an alternating map along the coefficient-field inclusion. -/
def restrictAlternating {N : Type*} [AddCommGroup N] [Module K N] [Module ℚ N]
    [IsScalarTower ℚ K N] {n : ℕ} (a : V [⋀^Fin n]→ₗ[K] N) :
    V [⋀^Fin n]→ₗ[ℚ] N where
  toMultilinearMap := a.toMultilinearMap.restrictScalars ℚ
  map_eq_zero_of_eq' := a.map_eq_zero_of_eq'

/-- The universal rational map sending a rational wedge to the same wedge over K. -/
def quotient (n : ℕ) : (⋀[ℚ]^n V) →ₗ[ℚ] (⋀[K]^n V) :=
  exteriorPower.alternatingMapLinearEquiv
    (restrictAlternating (exteriorPower.ιMulti K n (M := V)))

/-- Scalar restriction sends each pure wedge to the identical list of vectors. -/
theorem quotient_ιMulti (n : ℕ) (v : Fin n → V) :
    quotient n (exteriorPower.ιMulti ℚ n v) = exteriorPower.ιMulti K n v := by
  rw [quotient, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- In positive degree, coefficients can be absorbed into one wedge factor. -/
theorem quotient_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (quotient (K := K) (V := V) n) := by
  classical
  intro x
  have hx : x ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K n (M := V))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  have hall : ∀ a : K, a • x ∈ LinearMap.range (quotient (K := K) (V := V) n) := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        intro a
        refine ⟨exteriorPower.ιMulti ℚ n (Function.update v ⟨0, hn⟩ (a • v ⟨0, hn⟩)), ?_⟩
        rw [quotient_ιMulti, (exteriorPower.ιMulti K n).map_update_smul,
          Function.update_eq_self]
    | zero =>
        intro a
        rw [smul_zero]
        exact Submodule.zero_mem _
    | add y z hy hz iy iz =>
        intro a
        rw [smul_add]
        exact Submodule.add_mem _ (iy a) (iz a)
    | smul a y hy iy =>
        intro b
        rw [smul_smul]
        exact iy (b * a)
  exact LinearMap.mem_range.mp (by simpa only [one_smul] using hall 1)

/-- Dualizing the positive-degree exterior quotient gives an injection of rational forms. -/
theorem quotient_dualMap_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (quotient (K := K) (V := V) n).dualMap :=
  LinearMap.dualMap_injective_of_surjective (quotient_surjective n hn)

#print axioms restrictAlternating
#print axioms quotient
#print axioms quotient_ιMulti
#print axioms quotient_surjective
#print axioms quotient_dualMap_injective

end HodgeBlocks.ExteriorRestriction

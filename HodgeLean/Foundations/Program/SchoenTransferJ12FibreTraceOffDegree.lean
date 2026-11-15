import HodgeLean.Foundations.Program.SchoenTransferJ12FibreTrace

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Program
attribute [local irreducible] rationalProductCohomologyEquiv cohomologyMap

/-- Fibre contraction discards every external summand outside its specified fibre degree.
Source: the field-coefficient Künneth direct sum and its actual coordinate projection. -/
theorem s4_selected_fibre_trace_off_degree
    (T Y : TopCat.{0}) (hY : ∀ p : ℕ, Module.Finite ℚ (Cohomology ℚ Y p))
    (m n q r : ℕ) (h : q + r = m + n) (hq : q ≠ m)
    (I : Cohomology ℚ Y m ≃ₗ[ℚ] ℚ)
    (b : Cohomology ℚ Y q) (a : Cohomology ℚ T r) :
    s4_selected_fibre_trace T Y hY m n I
      (cup (TopCat.of (T × Y)) h
        (cohomologyMap ℚ q (productSecond T Y) b)
        (cohomologyMap ℚ r (productFirst T Y) a)) = 0 := by
  let swap : TopCat.of (Y × T) ⟶ TopCat.of (T × Y) :=
    TopCat.ofHom ⟨Prod.swap, continuous_swap⟩
  have h1 : cohomologyMap ℚ q swap (cohomologyMap ℚ q (productSecond T Y) b) =
      cohomologyMap ℚ q (productFirst Y T) b := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have h2 : cohomologyMap ℚ r swap (cohomologyMap ℚ r (productFirst T Y) a) =
      cohomologyMap ℚ r (productSecond Y T) a := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have hs (t : ℕ) (ht : q + r = t) :
      rationalProductCohomologyEquiv Y T hY t
        (DirectSum.lof ℚ (tensorDegreeIndex t)
          (fun k => Cohomology ℚ Y k.val.1 ⊗[ℚ] Cohomology ℚ T k.val.2)
          ⟨(q, r), Finset.mem_antidiagonal.mpr ht⟩ (b ⊗ₜ[ℚ] a)) =
      cup (TopCat.of (Y × T)) ht
        (cohomologyMap ℚ q (productFirst Y T) b)
        (cohomologyMap ℚ r (productSecond Y T) a) := by
    subst t
    exact rationalProductCohomologyEquiv_tmul Y T hY q r b a
  have hne : (⟨(q, r), Finset.mem_antidiagonal.mpr h⟩ : tensorDegreeIndex (m + n)) ≠
      ⟨(m, n), Finset.mem_antidiagonal.mpr rfl⟩ := by
    intro he
    exact hq (congrArg (fun k : tensorDegreeIndex (m + n) => k.val.1) he)
  unfold s4_selected_fibre_trace
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [cohomologyMap_cup, h1, h2, ← hs _ h, LinearEquiv.symm_apply_apply]
  simp [DirectSum.component.of, hne]

#print axioms s4_selected_fibre_trace_off_degree
end HodgeLean.Foundations.Program

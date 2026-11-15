import HodgeLean.Foundations.Singular.RationalProductCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Program

/-- Fibre contraction using finite rational cohomology of the actual fibre.
Source: Hatcher, Algebraic Topology, §3.2, field-coefficient Künneth. -/
def s4_selected_fibre_trace (T Y : TopCat.{0})
    (hY : ∀ p : ℕ, Module.Finite ℚ (Cohomology ℚ Y p))
    (m n : ℕ) (I : Cohomology ℚ Y m ≃ₗ[ℚ] ℚ) :
    Cohomology ℚ (TopCat.of (T × Y)) (m + n) →ₗ[ℚ] Cohomology ℚ T n :=
  (TensorProduct.lid ℚ (Cohomology ℚ T n)).toLinearMap ∘ₗ
    TensorProduct.map I.toLinearMap LinearMap.id ∘ₗ
    DirectSum.component ℚ (tensorDegreeIndex (m + n))
      (fun a => Cohomology ℚ Y a.1.1 ⊗[ℚ] Cohomology ℚ T a.1.2)
      ⟨(m, n), Finset.mem_antidiagonal.mpr rfl⟩ ∘ₗ
    (rationalProductCohomologyEquiv Y T hY (m + n)).symm.toLinearMap ∘ₗ
    cohomologyMap ℚ (m + n)
      (TopCat.ofHom (X := TopCat.of (Y × T)) (Y := TopCat.of (T × Y))
        ⟨Prod.swap, continuous_swap⟩)

/-- The fibre contraction evaluates an ordered external cup by its specified fibre integral.
Source: Hatcher, Algebraic Topology, §3.2, external cup products. -/
theorem s4_selected_fibre_trace_cross (T Y : TopCat.{0})
    (hY : ∀ p : ℕ, Module.Finite ℚ (Cohomology ℚ Y p))
    (m n : ℕ) (I : Cohomology ℚ Y m ≃ₗ[ℚ] ℚ)
    (b : Cohomology ℚ Y m) (a : Cohomology ℚ T n) :
    s4_selected_fibre_trace T Y hY m n I
      (cup (TopCat.of (T × Y)) rfl
        (cohomologyMap ℚ m (productSecond T Y) b)
        (cohomologyMap ℚ n (productFirst T Y) a)) = I b • a := by
  let swap : TopCat.of (Y × T) ⟶ TopCat.of (T × Y) :=
    TopCat.ofHom ⟨Prod.swap, continuous_swap⟩
  have h1 : cohomologyMap ℚ m swap
      (cohomologyMap ℚ m (productSecond T Y) b) =
      cohomologyMap ℚ m (productFirst Y T) b := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have h2 : cohomologyMap ℚ n swap
      (cohomologyMap ℚ n (productFirst T Y) a) =
      cohomologyMap ℚ n (productSecond Y T) a := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have hs := rationalProductCohomologyEquiv_tmul Y T hY m n b a
  unfold s4_selected_fibre_trace
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [cohomologyMap_cup, h1, h2, ← hs, LinearEquiv.symm_apply_apply,
    DirectSum.component.lof_self]
  simp

#print axioms s4_selected_fibre_trace_cross

end HodgeLean.Foundations.Program

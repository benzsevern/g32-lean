import HodgeLean.Foundations.Program.SchoenTransferJ12ProductNaturality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Program
attribute [local irreducible] rationalProductCohomologyEquiv cohomologyMap

/-- The specified finite-fibre contraction commutes with pullback along every actual base map.
Source: Hatcher, Algebraic Topology, §3.2, naturality of field-coefficient Künneth. -/
theorem s4_selected_fibre_trace_naturality
    (Y U T : TopCat.{0}) (f : U ⟶ T)
    (hY : ∀ p : ℕ, Module.Finite ℚ (Cohomology ℚ Y p))
    (m n : ℕ) (I : Cohomology ℚ Y m ≃ₗ[ℚ] ℚ)
    (c : Cohomology ℚ (TopCat.of (T × Y)) (m + n)) :
    s4_selected_fibre_trace U Y hY m n I
        (cohomologyMap ℚ (m + n) (s4_selected_product_map f (𝟙 Y)) c) =
      cohomologyMap ℚ n f (s4_selected_fibre_trace T Y hY m n I c) := by
  classical
  let r := m + n
  let k : tensorDegreeIndex r := ⟨(m, n), Finset.mem_antidiagonal.mpr rfl⟩
  let V (X : TopCat.{0}) (a : tensorDegreeIndex r) :=
    Cohomology ℚ Y a.1.1 ⊗[ℚ] Cohomology ℚ X a.1.2
  let E (X : TopCat.{0}) := rationalProductCohomologyEquiv Y X hY r
  let C (X : TopCat.{0}) : (⨁ a, V X a) →ₗ[ℚ] Cohomology ℚ X n :=
    (TensorProduct.lid ℚ (Cohomology ℚ X n)).toLinearMap ∘ₗ
      TensorProduct.map I.toLinearMap LinearMap.id ∘ₗ
      DirectSum.component ℚ _ (V X) k
  let F : (⨁ a, V T a) →ₗ[ℚ] (⨁ a, V U a) :=
    DirectSum.lmap (fun a => TensorProduct.map LinearMap.id
      (cohomologyMap ℚ a.1.2 f))
  have hC : (C U).comp F = (cohomologyMap ℚ n f).comp (C T) := by
    apply DirectSum.linearMap_ext ℚ
    intro a
    apply TensorProduct.ext'
    intro b x
    by_cases ha : a = k
    · subst a
      simp [C, F, V, k, LinearMap.comp_apply]
    · simp [C, F, LinearMap.comp_apply, DirectSum.component.of, ha]
  have hcoordinates (x : Cohomology ℚ (TopCat.of (Y × T)) r) :
      (E U).symm (cohomologyMap ℚ r (s4_selected_product_map (𝟙 Y) f) x) =
        F ((E T).symm x) := by
    apply (E U).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := LinearMap.congr_fun (s4_selected_product_right_cohomology Y U T f hY r)
      ((E T).symm x)
    simpa only [E, F, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using h
  let swap (X : TopCat.{0}) : TopCat.of (Y × X) ⟶ TopCat.of (X × Y) :=
    TopCat.ofHom ⟨Prod.swap, continuous_swap⟩
  have hswap : cohomologyMap ℚ r (swap U)
      (cohomologyMap ℚ r (s4_selected_product_map f (𝟙 Y)) c) =
      cohomologyMap ℚ r (s4_selected_product_map (𝟙 Y) f)
        (cohomologyMap ℚ r (swap T) c) := by
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  change C U ((E U).symm (cohomologyMap ℚ r (swap U)
      (cohomologyMap ℚ r (s4_selected_product_map f (𝟙 Y)) c))) =
    cohomologyMap ℚ n f (C T ((E T).symm (cohomologyMap ℚ r (swap T) c)))
  rw [hswap, hcoordinates]
  exact LinearMap.congr_fun hC ((E T).symm (cohomologyMap ℚ r (swap T) c))

#print axioms s4_selected_fibre_trace_naturality

end HodgeLean.Foundations.Program

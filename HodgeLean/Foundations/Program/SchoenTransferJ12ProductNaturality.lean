import HodgeLean.Foundations.Program.SchoenTransferJ12FibreTrace

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Program

/-- The actual continuous map of two specified product factors.
Source: the product topology universal property. -/
def s4_selected_product_map {U V X Y : TopCat.{0}} (f : U ⟶ X) (g : V ⟶ Y) :
    TopCat.of (U × V) ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun z => (f z.1, g z.2),
    (f.hom.continuous.comp continuous_fst).prodMk
      (g.hom.continuous.comp continuous_snd)⟩

/-- The actual finite-factor product decomposition commutes with pullback in its other factor.
Source: Hatcher, Algebraic Topology, §3.2, naturality of external cup products. -/
theorem s4_selected_product_right_cohomology
    (Y U T : TopCat.{0}) (f : U ⟶ T)
    (hY : ∀ p : ℕ, Module.Finite ℚ (Cohomology ℚ Y p)) (r : ℕ) :
    (cohomologyMap ℚ r (s4_selected_product_map (𝟙 Y) f)).comp
        (rationalProductCohomologyEquiv Y T hY r).toLinearMap =
      (rationalProductCohomologyEquiv Y U hY r).toLinearMap.comp
        (DirectSum.lmap (fun k : tensorDegreeIndex r =>
          TensorProduct.map (LinearMap.id : Cohomology ℚ Y k.1.1 →ₗ[ℚ] _)
            (cohomologyMap ℚ k.1.2 f))) := by
  classical
  apply DirectSum.linearMap_ext ℚ
  rintro ⟨⟨p, q⟩, hpq⟩
  apply TensorProduct.ext'
  intro b a
  have h : p + q = r := Finset.mem_antidiagonal.mp hpq
  subst r
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    DirectSum.lmap_lof, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [rationalProductCohomologyEquiv_tmul, rationalProductCohomologyEquiv_tmul,
    cohomologyMap_cup]
  congr 1 <;>
    simp only [← LinearMap.comp_apply, ← cohomologyMap_comp] <;> rfl

#print axioms s4_selected_product_right_cohomology

end HodgeLean.Foundations.Program

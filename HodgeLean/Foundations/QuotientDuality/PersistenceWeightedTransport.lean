import HodgeLean.Foundations.QuotientDuality.PersistenceCohomologyInjection
import HodgeLean.Foundations.QuotientDuality.PersistenceTransportObstruction

/-! Weighted transport through the natural singular coefficient comparison. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge
open scoped TensorProduct
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_weighted_transport_of_complex_preimages
    (X W : Over (Spec ↧ℂ)) (d₀ : X ⟶ X) (d : W ⟶ W) (f : W ⟶ X)
    (m : ℕ) [NeZero m] (hd : End.of d ^ m = 1)
    (n : ℕ) [Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint X)) n)]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (hl : ∀ v : Cohomology ℂ (TopCat.of (ComplexPoint W)) n,
      s2e_pullback ℂ d n v = ζ⁻¹ • v →
      ∃! u : Cohomology ℂ (TopCat.of (ComplexPoint X)) n,
        s2e_pullback ℂ d₀ n u = ζ⁻¹ • u ∧ s2e_pullback ℂ f n u = v)
    (cl : Cohomology ℚ (TopCat.of (ComplexPoint W)) n)
    (hnonzero : s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) n cl)) ≠ 0) :
    let v := s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
      (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) n cl))
    ∃! u : ℂ ⊗[ℚ] Cohomology ℚ (TopCat.of (ComplexPoint X)) n,
      u ≠ 0 ∧ (s2e_pullback ℚ d₀ n).baseChange ℂ u = ζ⁻¹ • u ∧
        (s2e_pullback ℚ f n).baseChange ℂ u = v := by
  dsimp only
  let v := s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
    (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
      (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) n cl))
  have hv : (s2e_pullback ℚ d n).baseChange ℂ v = ζ⁻¹ • v := by
    have h := persistence_weighted_deck_inverse W d m hd n ζ hζ cl
    have hh := congrArg (fun x => ζ⁻¹ • x) h
    simpa only [smul_smul, inv_mul_cancel₀ (hζ.ne_zero (NeZero.ne m)), one_smul] using hh
  obtain ⟨u, hu, hunique⟩ := persistence_eigen_preimages_of_coefficient_comparison
    ((s2e_pullback ℚ d₀ n).baseChange ℂ) ((s2e_pullback ℚ d n).baseChange ℂ)
    (s2e_pullback ℂ d₀ n) (s2e_pullback ℂ d n)
    ((s2e_pullback ℚ f n).baseChange ℂ) (s2e_pullback ℂ f n)
    (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n)
    (cohomologyBaseChange (TopCat.of (ComplexPoint W)) n)
    (cohomologyBaseChange_bijective _ n) (persistence_cohomology_baseChange_injective _ n)
    (cohomologyBaseChange_natural (TopCat.ofHom (Point.continuousMap d₀)) n)
    (cohomologyBaseChange_natural (TopCat.ofHom (Point.continuousMap d)) n)
    (cohomologyBaseChange_natural (TopCat.ofHom (Point.continuousMap f)) n)
    ζ⁻¹ hl v hv
  refine ⟨u, ⟨?_, hu⟩, ?_⟩
  · intro hz
    apply hnonzero
    exact hu.2.symm.trans (hz ▸ map_zero _)
  · intro z hz
    exact hunique z hz.2

end HodgeLean.Foundations.QuotientDuality

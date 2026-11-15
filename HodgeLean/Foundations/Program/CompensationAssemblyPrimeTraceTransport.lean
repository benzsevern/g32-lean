import HodgeLean.Foundations.Program.CompensationAssemblyPrimeRelativeTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_prime_product_support_map (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (x : (A ⊗ Y).left) :
    cq_pairProduct (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
        ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) :
          Set (ComplexPoint A))ᶜ)) (TopCat.of (ComplexPoint Y)) ⟶
      TopPair.ofSubset (X := TopCat.of (ComplexPoint (A ⊗ Y)))
        ((cycleComponentAnalyticClosedSupport (A ⊗ Y) x :
          Set (ComplexPoint (A ⊗ Y)))ᶜ) := by
  let h := HodgeLean.Foundations.complexPointProdHomeomorph A Y
  let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
    ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) : Set (ComplexPoint A))ᶜ)
  let Q := TopPair.ofSubset (X := TopCat.of (ComplexPoint (A ⊗ Y)))
    ((cycleComponentAnalyticClosedSupport (A ⊗ Y) x : Set (ComplexPoint (A ⊗ Y)))ᶜ)
  let f : (cq_pairProduct P (TopCat.of (ComplexPoint Y))).fst ⟶ Q.fst :=
    TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hf : ∀ p : P.snd × ComplexPoint Y,
      h.symm (p.1.1, p.2) ∉ cycleComponentAnalyticClosedSupport (A ⊗ Y) x := by
    intro p hp
    have hs := cq_component_support_map (fst A Y) x (h.symm (p.1.1, p.2)) hp
    have he : Point.map (fst A Y) (h.symm (p.1.1, p.2)) = p.1.1 :=
      congrArg Prod.fst (h.apply_symm_apply (p.1.1, p.2))
    rw [he] at hs
    exact p.1.2 hs
  let g : (cq_pairProduct P (TopCat.of (ComplexPoint Y))).snd ⟶ Q.snd :=
    TopCat.ofHom ⟨fun p => ⟨h.symm (p.1.1, p.2), hf p⟩,
      (h.symm.continuous.comp (continuous_subtype_val.prodMap continuous_id)).subtype_mk _⟩
  exact TopPair.ofHom f g rfl

def cq_prime_product_relative_class (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (x : (A ⊗ Y).left) {p : ℕ} (hx : Order.coheight x = p) :
    RelativeCohomology ℚ
      (cq_pairProduct (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
        ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) :
          Set (ComplexPoint A))ᶜ)) (TopCat.of (ComplexPoint Y))) (2 * p) :=
  relativeCohomologyMap ℚ (2 * p) (cq_prime_product_support_map A Y x)
    (ccm16_supportedComparison (A ⊗ Y) (cycleComponentAnalyticClosedSupport (A ⊗ Y) x)
      (2 * p) (cycleComponentSupportedInjectiveClass (A ⊗ Y) x hx))

set_option backward.isDefEq.respectTransparency false in
theorem cq_prime_product_relative_class_absolute (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (x : (A ⊗ Y).left) {p : ℕ} (hx : Order.coheight x = p) :
    relativeCohomologyToAbsolute ℚ _ (2 * p) (cq_prime_product_relative_class A Y x hx) =
      cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
        (2 * p) (cupComparison (A ⊗ Y) (2 * p)
          (cycleComponentSheafClass (A ⊗ Y) x hx)) := by
  have hc : relativeCohomologyToAbsolute ℚ _ (2 * p)
      (ccm16_supportedComparison (A ⊗ Y) (cycleComponentAnalyticClosedSupport (A ⊗ Y) x)
        (2 * p) (cycleComponentSupportedInjectiveClass (A ⊗ Y) x hx)) =
      cupComparison (A ⊗ Y) (2 * p) (cycleComponentSheafClass (A ⊗ Y) x hx) :=
    (ccm16_supportedComparison_forget (A ⊗ Y)
      (cycleComponentAnalyticClosedSupport (A ⊗ Y) x) (2 * p)
      (cycleComponentSupportedInjectiveClass (A ⊗ Y) x hx)).trans
        (bh11_cupComparison_eq_raw (A ⊗ Y) (2 * p)
          (cycleComponentSheafClass (A ⊗ Y) x hx)).symm
  rw [cq_prime_product_relative_class, cq_relativeToAbsolute_naturality, hc]
  exact (cq_cohomologyHomeomorphEquiv_apply
    (HodgeLean.Foundations.complexPointProdHomeomorph A Y) (2 * p) _).symm

end HodgeLean.Foundations.Program

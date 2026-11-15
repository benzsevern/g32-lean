import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentEtale
import HodgeLean.Foundations.Program.SchoenTransferQ3EtaleRefinement

/-! The smooth etale pair of actual reduced support components. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original finite map induces a finite surjection of reduced support
components with a dense smooth etale source and target restriction. -/
theorem s4_q3_reduced_component_smooth_etale_map
    {X W : Over (Spec ↧ℂ)} [LocallyOfFinitePresentation W.hom]
    (q : X ⟶ W) [IsFinite q.left] (p : X.left) :
    let XC : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal X.left p).subschemeι ≫ X.hom)
    let WC : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal W.left (q.left p)).subschemeι ≫ W.hom)
    ∃ f : XC ⟶ WC,
      f.left ≫ (ccm3_primeIdeal W.left (q.left p)).subschemeι =
        (ccm3_primeIdeal X.left p).subschemeι ≫ q.left ∧
      IsFinite f.left ∧ Function.Surjective f.left ∧
      ∃ U : WC.left.Opens, Dense (U : Set WC.left) ∧
        Smooth (U.ι ≫ WC.hom) ∧ Etale (f.left ∣_ U) ∧
        Smooth ((f.left ⁻¹ᵁ U).ι ≫ XC.hom) := by
  let I := ccm3_primeIdeal X.left p
  let J := ccm3_primeIdeal W.left (q.left p)
  let XC : Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ X.hom)
  let WC : Over (Spec ↧ℂ) := Over.mk (J.subschemeι ≫ W.hom)
  obtain ⟨f, hf, hfinite, hsurj, U₀, hdense, hEt⟩ :=
    s4_q3_reduced_component_dense_etale_open q p
  let fC : XC ⟶ WC := Over.homMk f (by
    change f ≫ J.subschemeι ≫ W.hom = I.subschemeι ≫ X.hom
    rw [← Category.assoc, hf, Category.assoc, Over.w q])
  letI : IsIntegral WC.left := inferInstanceAs (IsIntegral (cycleComponent W.left (q.left p)))
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : LocallyOfFinitePresentation WC.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (J.subschemeι ≫ W.hom))
  obtain ⟨U, hU, hUU₀, hsmooth, hetale, hsource⟩ :=
    s4_q3_smooth_etale_refinement fC U₀ hdense hEt
  exact ⟨fC, hf, hfinite, hsurj, U, hU, hsmooth, hetale, hsource⟩

end HodgeLean.Foundations.Program

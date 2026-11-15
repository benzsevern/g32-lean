import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentMap
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexGenericEtaleHelpers

/-! Generic tangent comparison on the actual reduced support components. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual reduced-component map is finite etale over a dense target
open in characteristic zero, with the original inclusion square retained. -/
theorem s4_q3_reduced_component_dense_etale_open
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom]
    (q : X ⟶ W) [IsFinite q.left] (p : X.left) :
    ∃ f : (ccm3_primeIdeal X.left p).subscheme ⟶
        (ccm3_primeIdeal W.left (q.left p)).subscheme,
      f ≫ (ccm3_primeIdeal W.left (q.left p)).subschemeι =
        (ccm3_primeIdeal X.left p).subschemeι ≫ q.left ∧
      IsFinite f ∧ Function.Surjective f ∧
      ∃ U : (ccm3_primeIdeal W.left (q.left p)).subscheme.Opens,
        Dense (U : Set (ccm3_primeIdeal W.left (q.left p)).subscheme) ∧ Etale (f ∣_ U) := by
  let I := ccm3_primeIdeal X.left p
  let J := ccm3_primeIdeal W.left (q.left p)
  obtain ⟨f, hf, hfinite, hsurj⟩ := s4_q3_finite_map_on_reduced_components q.left p
  let XC : Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ X.hom)
  let WC : Over (Spec ↧ℂ) := Over.mk (J.subschemeι ≫ W.hom)
  let fC : XC ⟶ WC := Over.homMk f (by
    change f ≫ J.subschemeι ≫ W.hom = I.subschemeι ≫ X.hom
    rw [← Category.assoc, hf, Category.assoc, Over.w q])
  letI : IsIntegral XC.left := inferInstanceAs (IsIntegral (cycleComponent X.left p))
  letI : IsIntegral WC.left := inferInstanceAs (IsIntegral (cycleComponent W.left (q.left p)))
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : LocallyOfFiniteType WC.hom := inferInstanceAs (LocallyOfFiniteType (J.subschemeι ≫ W.hom))
  letI : IsLocallyNoetherian WC.left := LocallyOfFiniteType.isLocallyNoetherian WC.hom
  letI : IsFinite fC.left := hfinite
  letI : Surjective fC.left := ⟨hsurj⟩
  obtain ⟨U, hU, hfinU, hEt⟩ := s2e_c1_complex_finite_exists_etale_base_open XC WC fC
  exact ⟨f, hf, hfinite, hsurj, U, U.isOpen.dense hU, hEt⟩

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.G32Native.EulerModel.ComponentCupComparison
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateHyperplaneClass
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateCohomology

/-! # Exact canonical classes of literal native coordinate hyperplanes -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The singleton coordinate intersection on the identity native projective model is the literal residue hyperplane ideal. -/
theorem nativeCoordinateSingleton_ideal (k : ℕ) (j : Fin (k + 1)) :
    (s2e_s2b_intersectionIdeal k {j}).comap
        (Iso.refl (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).hom.left =
      s2e_s2b_residueIdeal k j := by
  classical
  change (s2e_s2b_intersectionIdeal k {j}).comap (𝟙 _) = _
  rw [Scheme.IdealSheafData.comap_id]
  simp only [s2e_s2b_intersectionIdeal, Finset.mem_singleton, iSup_iSup_eq_left]

#print axioms nativeCoordinateSingleton_ideal
/-- The canonical singleton coordinate class retains the exact absolute class of every normalized literal native hyperplane coclass. -/
theorem nativeCoordinateSingleton_cupComparison (k : ℕ) (hk : 0 < k) (j : Fin (k + 1))
    [IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).left]
    [Smooth (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom]
    [IsProjective (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom] :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let I := s2e_s2b_residueIdeal k j
    let jI := s2c_subschemeι PP I
    ∃ (hI : IsIntegral (s2c_subscheme PP I).left),
      letI := hI
      ∀ c : s2e_supportedClass PP (s2e_componentCycle jI ℚ) 1,
        a3b4_IsCycleClass PP.hom (s2e_componentCycle jI ℚ) 1 c →
        cupComparison PP 2 (coordinate_class_at_degree PP k (Iso.refl PP) {j}
          (by simp only [Finset.card_singleton]; omega) 1 (Finset.card_singleton j)) =
            s2e_classToAbsolute PP (s2e_componentCycle jI ℚ) 1 c := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let I := s2e_s2b_residueIdeal k j
  let jI := s2c_subschemeι PP I
  obtain ⟨hI, _, hcod, _⟩ := nativeResidueHyperplane_class k hk j
  letI := hI
  refine ⟨hI, ?_⟩
  intro c hc
  have hId := nativeCoordinateSingleton_ideal k j
  have hbound : ({j} : Finset (Fin (k + 1))).card ≤ k := by
    simp only [Finset.card_singleton]; omega
  obtain ⟨hKT, _, hcodT, _⟩ := coordinate_intersection_class PP k (Iso.refl PP) {j} hbound
  letI := hKT
  have hcodOne : Order.coheight ((s2c_subschemeι PP
      ((s2e_s2b_intersectionIdeal k {j}).comap (Iso.refl PP).hom.left)).left
        (genericPoint (s2c_subscheme PP
          ((s2e_s2b_intersectionIdeal k {j}).comap (Iso.refl PP).hom.left)).left)) = 1 := by
    simpa only [Finset.card_singleton, Nat.cast_one] using hcodT
  rw [coordinate_class_at_degree_eq PP k (Iso.refl PP) {j} _ 1
    (Finset.card_singleton j) hcodOne]
  have hcmp (K : PP.left.IdealSheafData)
      (hK : IsIntegral (s2c_subscheme PP K).left) (heq : K = I) :
      letI := hK
      ∀ hcK : Order.coheight ((s2c_subschemeι PP K).left
          (genericPoint (s2c_subscheme PP K).left)) = 1,
        cupComparison PP 2 (cycleComponentSheafClass PP
          ((s2c_subschemeι PP K).left (genericPoint (s2c_subscheme PP K).left)) hcK) =
            s2e_classToAbsolute PP (s2e_componentCycle jI ℚ) 1 c := by
    subst K
    intro hcK
    exact normalized_component_cupComparison jI 1 hcK c hc
  exact hcmp _ hKT hId hcodOne

#print axioms nativeCoordinateSingleton_cupComparison
end HodgeLean.Foundations.Program.G32Native.EulerModel

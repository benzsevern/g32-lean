import HodgeLean.Foundations.Program.SchoenTowerL1bRegularNeighborhoods
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerDominance

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Simultaneous Cartier equations have nonzero product under the exact retained generic section map. -/
theorem s2v_l1b_cartier_equations_generic_nonzero
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) [IsDominant η]
    {J : Type*} [Fintype J] (I : J → X.IdealSheafData)
    (x : X) (V : X.Opens) (hxV : x ∈ V)
    (hI : ∀ j, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty ((I j).ideal U ≃ₗ[Γ(X, U)] Γ(X, U))) :
    ∃ (U : X.affineOpens) (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) (g : J → Γ(X, U)),
      x ∈ U.1 ∧ U.1 ≤ V ∧ (∀ j, (I j).ideal U = Ideal.span {g j}) ∧
        (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom (∏ j, g j) ≠ 0 := by
  obtain ⟨U, hxU, hUV, g, hg⟩ := s2v_l1b_simultaneous_cartier_equations X I x V hxV hI
  haveI : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hηU : ⊤ ≤ η ⁻¹ᵁ U.1 := by
    intro z _
    change η z ∈ U.1
    rw [Subsingleton.elim z (genericPoint (Spec (.of K))), s2_dominant_genericPoint η]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (show Nonempty U.1 from inferInstance))
  refine ⟨U, hηU, g, hxU, hUV, fun j => (hg j).1, ?_⟩
  have hprod : (∏ j, g j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hg j).2
  intro hz
  apply hprod
  exact s2v_l1b_dominant_section_map_injective X η U.1 hηU
    (hz.trans (map_zero (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom).symm)

end HodgeLean.Foundations.Program

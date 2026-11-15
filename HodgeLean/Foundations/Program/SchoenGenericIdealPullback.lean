import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual proper ideal support on an integral scheme misses the generic point. -/
theorem s2_genericPoint_not_mem_idealSupport {X : Scheme.{0}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) : genericPoint X ∉ I.support := by
  intro hx
  apply hI
  apply top_le_iff.mp
  intro x _
  exact ((genericPoint_spec X).mem_closed_set_iff I.support.isClosed).mp hx (Set.mem_univ x)

/-- Pulling an actual ideal with proper support back along a dominant field point gives the unit ideal sheaf. -/
theorem s2_ideal_comap_dominant_fieldPoint {K : Type} [Field K]
    {X : Scheme.{0}} [IsIntegral X] (η : Spec (.of K) ⟶ X) [IsDominant η]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) : I.comap η = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change η x ∈ I.support ↔ False
  rw [Subsingleton.elim x (genericPoint (Spec (.of K))), s2_dominant_genericPoint η]
  exact iff_false_intro (s2_genericPoint_not_mem_idealSupport I hI)

/-- Every actual dominant field point makes an ideal of proper support locally free of rank one after pullback. -/
theorem s2_dominant_fieldPoint_cartier {K : Type} [Field K]
    {X : Scheme.{0}} [IsIntegral X] (η : Spec (.of K) ⟶ X) [IsDominant η]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤) :
    ∀ x : Spec (.of K), ∃ U : (Spec (.of K)).affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap η).ideal U) ≃ₗ[Γ(Spec (.of K), U)] Γ(Spec (.of K), U)) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  rw [s2_ideal_comap_dominant_fieldPoint η I hI]
  exact ⟨Submodule.topEquiv⟩

end HodgeLean.Foundations.Program

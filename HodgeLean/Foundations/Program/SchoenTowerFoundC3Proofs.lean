import HodgeLean.Foundations.Program.SchoenFieldNormalizationFinite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finiteness propagates along the specified retained-field tower.
Source: EGA II, 6.3, normalization; Mathlib, `LocallyQuasiFinite.of_comp`;
`s2_fieldNormalization_finite`. -/
theorem s2t_normalization_tower_finite_aux {K : Type} [Field K] [CharZero K]
    (r : ℕ) (B : Fin (r + 1) → Scheme.{0})
    [∀ i, IsIntegral (B i)] [∀ i, IsLocallyNoetherian (B i)]
    (hn : ∀ i, zmtiso_IsNormal (B i))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, Spec (.of K) ⟶ B i)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    [∀ i, IsDominant (η i)] [LocallyQuasiFinite (η 0)]
    (hη : ∀ i : Fin r, η i.succ ≫ b i = η i.castSucc) :
    ∀ i, LocallyQuasiFinite (η i) ∧ IsFinite (η i).fromNormalization := by
  have hq : ∀ i, LocallyQuasiFinite (η i) := by
    intro i
    induction i using Fin.induction with
    | zero => infer_instance
    | succ i ih =>
      haveI := ih
      haveI : LocallyQuasiFinite (η i.succ ≫ b i) := by
        rw [hη i]
        exact ih
      exact LocallyQuasiFinite.of_comp (η i.succ) (b i)
  intro i
  haveI := hq i
  exact ⟨inferInstance, s2_fieldNormalization_finite (B i) (hn i) (η i)⟩

end HodgeLean.Foundations.Program

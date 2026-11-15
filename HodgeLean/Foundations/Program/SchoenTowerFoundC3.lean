import HodgeLean.Foundations.Program.SchoenTowerFoundC3Proofs

/-! # C3: finite normalization along a retained-field tower
Implication from normal noetherian bases and a compatible dominant field family.
This first piece derives quasi-finiteness at later stages from stage zero.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finiteness propagates along the specified retained-field tower.
Source: EGA II, 6.3, normalization; Mathlib, `LocallyQuasiFinite.of_comp`;
`s2_fieldNormalization_finite`. -/
theorem s2t_normalization_tower_finite {K : Type} [Field K] [CharZero K]
    (r : ℕ) (B : Fin (r + 1) → Scheme.{0})
    [∀ i, IsIntegral (B i)] [∀ i, IsLocallyNoetherian (B i)]
    (hn : ∀ i, zmtiso_IsNormal (B i))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, Spec (.of K) ⟶ B i)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    [∀ i, IsDominant (η i)] [LocallyQuasiFinite (η 0)]
    (hη : ∀ i : Fin r, η i.succ ≫ b i = η i.castSucc) :
    ∀ i, LocallyQuasiFinite (η i) ∧ IsFinite (η i).fromNormalization :=
  s2t_normalization_tower_finite_aux r B hn b η hη

example := @s2t_normalization_tower_finite

end HodgeLean.Foundations.Program

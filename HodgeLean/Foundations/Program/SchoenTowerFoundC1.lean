import HodgeLean.Foundations.Program.SchoenTowerFoundC1Proofs

/-! # C1: generic lifts through specified modifications
Implication from the explicit invertible-image-ideal universal properties.
The source is the retained function field of W at every index.
HC no distance; AV milestone no distance.
This unit supplies no normalization, deck action or off-centre scheme isomorphism.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A retained function field lifts uniquely through a specified finite tower.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.14;
Stacks Project, Section 31.33, Lemmas 31.33.4 and 31.33.5 (Tag 01OF). -/
theorem s2t_generic_tower (W : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, IsProjective (B i).hom]
    (β : W ⟶ B 0) [IsFinite β.left] [IsDominant β.left]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (K : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hK : ∀ i, (K i).support ≠ ⊤)
    (huniv : ∀ i (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((K i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f) :
    ∃! η : ∀ i, Spec W.left.functionField ⟶ (B i).left,
      η 0 = W.left.fromSpecStalk (genericPoint W.left) ≫ β.left ∧
      (∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc) ∧
      (∀ i, IsDominant (η i) ∧ QuasiCompact (η i) ∧ QuasiSeparated (η i)) :=
  s2t_generic_tower_aux W r B β b K hK huniv

example := @s2t_generic_tower

end HodgeLean.Foundations.Program

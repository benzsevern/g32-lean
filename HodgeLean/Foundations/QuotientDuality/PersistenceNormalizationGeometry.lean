import HodgeLean.Foundations.Program.SchoenTowerFoundC3
import HodgeLean.Foundations.Program.SchoenTowerI2bTowerGeneric
import HodgeLean.Foundations.Program.SchoenTowerI2bGenericSuppliers

/-! Finiteness and properness of retained normalization transitions. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_normalization_transition_proper
    {T U : Scheme} (B' B : Over (Spec ↧ℂ))
    [IsProper B'.hom] [IsSeparated B.hom]
    (η' : T ⟶ B'.left) (η : U ⟶ B.left)
    [QuasiCompact η'] [QuasiSeparated η'] [QuasiCompact η] [QuasiSeparated η]
    [IsFinite η'.fromNormalization]
    (w : s2b_normalizationOver B' η' ⟶ s2b_normalizationOver B η) :
    IsProper w.left := by
  haveI : IsProper (s2b_normalizationOver B' η').hom :=
    inferInstanceAs (IsProper (η'.fromNormalization ≫ B'.hom))
  haveI : IsSeparated (s2b_normalizationOver B η).hom :=
    inferInstanceAs (IsSeparated (η.fromNormalization ≫ B.hom))
  haveI : IsProper (w.left ≫ (s2b_normalizationOver B η).hom) := by
    rw [Over.w w]
    infer_instance
  exact IsProper.of_comp w.left (s2b_normalizationOver B η).hom

lemma persistence_normalization_tower_finite
    {L : Type} [Field L] [CharZero L] {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec ↧L ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    [LocallyQuasiFinite (η 0)]
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (hdom : IsDominant (η 0)) : ∀ i, IsFinite (η i).fromNormalization := by
  haveI : ∀ i, IsDominant (η i) :=
    s2v_i2b_tower_genericSource_dominant B b I hcartier hblowup η hη hdom
  have hf := s2t_normalization_tower_finite r (fun i => (B i).left)
    (fun i => zmtiso_normal_of_smooth (B i).left (B i).hom)
    (fun i => (b i).left) η hη
  exact fun i => (hf i).2

lemma persistence_initial_field_quasiFinite
    (W B Binit : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (β : W ⟶ B) [IsFinite β.left] (e : Binit ≅ B)
    (η : Spec W.left.functionField ⟶ Binit.left)
    (hη : η ≫ e.hom.left = W.left.fromSpecStalk (genericPoint W.left) ≫ β.left) :
    LocallyQuasiFinite η := by
  haveI : LocallyQuasiFinite
      (W.left.fromSpecStalk (genericPoint W.left) ≫ β.left) :=
    Scheme.Hom.quasiFiniteAt_iff.mp (β.left.quasiFiniteAt (genericPoint W.left))
  haveI : LocallyQuasiFinite (η ≫ e.hom.left) := by rw [hη]; infer_instance
  exact LocallyQuasiFinite.of_comp η e.hom.left

end HodgeLean.Foundations.QuotientDuality

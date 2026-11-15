import HodgeLean.Foundations.Program.G32Native.NormalizationDeck
import HodgeLean.Foundations.Program.SchoenCycleC1FunctionFieldActionHelpers
import HodgeLean.Foundations.Program.SchoenTowerFoundC1

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained deck map acts on the retained generic field with its specified order. -/
theorem g32w_generic_deck (W : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (d : W ⟶ W) [IsIso d] (m : ℕ) (hm : End.of d ^ m = 1) :
    ∃ u : Spec W.left.functionField ≅ Spec W.left.functionField,
      u.hom ≫ W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d.left ∧
      End.of u.hom ^ m = 1 := by
  let e := s2e_c1_fieldPullbackEquiv W.left d.left
  let u := Scheme.Spec.mapIso e.toCommRingCatIso.op
  have hu : u.hom ≫ W.left.fromSpecStalk (genericPoint W.left) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ d.left :=
    s2e_step1_fieldPullback_generic W.left d.left
  refine ⟨u, hu, ?_⟩
  apply End.ext
  apply (cancel_mono (W.left.fromSpecStalk (genericPoint W.left))).mp
  rw [← g32w_source_power u.hom _ d.left hu.symm]
  have hleft : End.of d.left ^ m = 1 := by
    have h := congrArg ((Over.forget (Spec ↧ℂ)).mapEnd _) hm
    rw [map_pow, map_one] at h
    exact h
  rw [hleft]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Uniqueness of the specified blow-up lifts fixes every generic map under the deck action. -/
theorem g32w_generic_tower_invariant
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, IsProjective (B i).hom]
    (β : W ⟶ B 0) [IsFinite β.left] [IsDominant β.left]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (K : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hK : ∀ i, (K i).support ≠ ⊤)
    (huniv : ∀ i (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((K i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! v : T ⟶ B i.succ, v ≫ b i = f)
    (η : ∀ i, Spec W.left.functionField ⟶ (B i).left)
    [∀ i, IsDominant (η i)] [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη0 : η 0 = W.left.fromSpecStalk (genericPoint W.left) ≫ β.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (u : Spec W.left.functionField ≅ Spec W.left.functionField)
    (hu0 : u.hom ≫ η 0 = η 0) : ∀ i, u.hom ≫ η i = η i := by
  obtain ⟨θ, hθ, huniq⟩ := s2t_generic_tower W r B β b K hK huniv
  have he : η = θ := huniq η ⟨hη0, hη, fun _ => ⟨inferInstance, inferInstance, inferInstance⟩⟩
  have he' : (fun i => u.hom ≫ η i) = θ := by
    apply huniq
    refine ⟨hu0.trans hη0, ?_, fun _ => ⟨inferInstance, inferInstance, inferInstance⟩⟩
    intro i
    rw [Category.assoc, hη]
  intro i
  exact congrFun (he'.trans he.symm) i

end HodgeLean.Foundations.Program

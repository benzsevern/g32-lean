import HodgeLean.Foundations.Program.SchoenCartierUniversalFieldLift

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A retained function field lifts uniquely through a specified finite tower.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.14;
Stacks Project, Section 31.33, Lemmas 31.33.4 and 31.33.5 (Tag 01OF). -/
theorem s2t_generic_tower_aux (W : Over (Spec ↧ℂ)) [IsIntegral W.left]
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
      (∀ i, IsDominant (η i) ∧ QuasiCompact (η i) ∧ QuasiSeparated (η i)) := by
  classical
  let η₀ := W.left.fromSpecStalk (genericPoint W.left) ≫ β.left
  haveI : IsDominant η₀ := by
    haveI := s2_genericPointMorphism_dominant W.left
    dsimp [η₀]
    infer_instance
  let step (i : Fin r)
      (p : {f : Spec W.left.functionField ⟶ (B i.castSucc).left // IsDominant f}) :
      {f : Spec W.left.functionField ⟶ (B i.succ).left //
        f ≫ (b i).left = p.val ∧ IsDominant f} := by
    haveI := p.property
    exact ⟨_, Classical.choose_spec
      (s2_cartierUniversal_fieldLift _ _ (b i) (K i) (hK i) (huniv i) p.val)⟩
  let data : ∀ i : Fin (r + 1),
      {f : Spec W.left.functionField ⟶ (B i).left // IsDominant f} :=
    Fin.induction ⟨η₀, inferInstance⟩
      (fun i p => ⟨(step i p).val, (step i p).property.2⟩)
  let η := fun i => (data i).val
  have hstep (i : Fin r) : η i.succ ≫ (b i).left = η i.castSucc :=
    (step i (data i.castSucc)).property.1
  refine ⟨η, ⟨rfl, hstep, ?_⟩, ?_⟩
  · intro i
    refine ⟨(data i).property, ?_, inferInstance⟩
    haveI : Subsingleton (Spec W.left.functionField) := by
      change Subsingleton (PrimeSpectrum W.left.functionField)
      infer_instance
    constructor
    intro U _ _
    exact Set.Subsingleton.isCompact (Set.subsingleton_of_subsingleton)
  · intro θ hθ
    funext i
    induction i using Fin.induction with
    | zero => exact hθ.1
    | succ i ih =>
      haveI := (data i.castSucc).property
      let T := Over.mk (η i.castSucc ≫ (B i.castSucc).hom)
      let f : T ⟶ B i.castSucc := Over.homMk (η i.castSucc)
      obtain ⟨u, hu, huniq⟩ := huniv i T f
        (s2_dominant_fieldPoint_cartier (η i.castSucc) (K i) (hK i))
      have hθb : θ i.succ ≫ (b i).left = η i.castSucc :=
        (hθ.2.1 i).trans ih
      let v : T ⟶ B i.succ := Over.homMk (θ i.succ) (by
        rw [← Over.w (b i), ← Category.assoc, hθb]
        rfl)
      let w : T ⟶ B i.succ := Over.homMk (η i.succ) (by
        rw [← Over.w (b i), ← Category.assoc, hstep]
        rfl)
      exact congrArg Over.Hom.left
        ((huniq v (Over.OverMorphism.ext hθb)).trans
          (huniq w (Over.OverMorphism.ext (hstep i))).symm)

end HodgeLean.Foundations.Program

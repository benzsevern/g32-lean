import HodgeLean.Foundations.Program.G32Native.JointPairedStagesRegularity
import HodgeLean.Foundations.Program.G32Native.SelectedPairedBaseInitialRegularity

/-! The regularity interface on the same stages as T5's blow-up construction. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Supply the full T6 family input for the literal selected points and quotient. -/
theorem joint_selected_paired_family
    (hstep : by_elab return (← Lean.getConstInfo ``joint_paired_stages_regularity).type.bindingDomain!)
    (Y Z B₀ : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀)
    (hinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! d : B₀ ⟶ T, γ ≫ d = f)
    (p₀ : Y ⟶ Z) (C : Type*) (eY : C → ComplexPoint Y)
    {n : ℕ} (y : Fin n → C) (σ : Fin (2 * r) ≃ Fin n)
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t)))) :
    ∃ (B : Fin (r + 1) → Over (Spec ↧ℂ))
      (e₀ : B 0 ≅ B₀)
      (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
      (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData),
      (∀ j, D 0 j = (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j))))).comap e₀.hom.left) ∧
      (∀ i, Smooth (B i).hom ∧ IsProjective (B i).hom ∧ IsIntegral (B i).left) ∧
      (∀ i (J : Finset (Fin (2 * r))),
        Smooth (s2c_subscheme (B i) (J.sup (D i))).hom ∧
        ∀ x : (s2c_subscheme (B i) (J.sup (D i))).left,
          ∃ U : (s2c_subscheme (B i) (J.sup (D i))).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι (B i) (J.sup (D i))).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
                U.toScheme.Modules))) ∧
      ∀ i : Fin r,
        let K := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩
        (∀ j, D i.succ j = s2c_strictTransform (b i).left (D i.castSucc j) K) ∧
        (∀ x : (B i.succ).left, ∃ U : (B i.succ).left.affineOpens,
          x ∈ U.1 ∧ Nonempty (((K.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
            Γ((B i.succ).left, U))) ∧
        (∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
          (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
            Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
          ∃! u : T ⟶ B i.succ, u ≫ b i = f) := by
  let D₀ := fun t => s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))
  let A : g32t5_BranchStage (Spec ↧ℂ) r := ⟨B₀, D₀⟩
  let stages := g32t5_stages A
  let B : Fin (r + 1) → Over (Spec ↧ℂ) := fun i => (stages i).1
  let b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc := fun i =>
    g32t5_stageTransition i (stages i.castSucc) (stages i.succ)
      (g32t5_stages_succ A i)
  let D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData := fun i => (stages i).2
  obtain ⟨hs, hp, hi, hJ⟩ := g32l4_selected_initial_regularity
    Y Z B₀ hdim h r γ hinv huniv p₀ C eY y σ hy
  have hreg := joint_paired_stages_regularity hstep A ⟨hs, hp, hi⟩ (fun J =>
    ⟨(hJ J).1, (hJ J).2.1⟩)
  refine ⟨B, Iso.refl B₀, b, D, ?_, ?_, ?_, ?_⟩
  · intro j
    change D₀ j = (D₀ j).comap (𝟙 B₀.left)
    exact (Scheme.IdealSheafData.comap_id _).symm
  · intro i
    exact (hreg i).1
  · intro i J
    exact (hreg i).2 J
  · intro i
    exact g32t5_stageTransition_spec i (stages i.castSucc) (stages i.succ)
      (g32t5_stages_succ A i)

#print axioms joint_selected_paired_family
end HodgeLean.Foundations.Program

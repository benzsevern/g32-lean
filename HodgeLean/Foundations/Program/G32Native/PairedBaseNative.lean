import HodgeLean.Foundations.Program.G32Native.PairedBaseInduction

/-! T01–T04 in the retained native telescope, from the GT family output. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Retain the GT choices and put their properties in native binder order.
The hypothesis is the literal output of the T5 construction target. -/
theorem g32t6_paired_base_native (Z B₀ : Over (Spec ↧ℂ)) (h r : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B₀)
    (z : Fin (2 * r) → ComplexPoint Z)
    (hFamily :
    ∃ (B : Fin (r + 1) → Over (Spec ↧ℂ))
      (e₀ : B 0 ≅ B₀)
      (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
      (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData),
      (∀ j, D 0 j = (s2c_branchIdeal Z B₀ h γ (z j)).comap e₀.hom.left) ∧
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
          ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    ) :
∃ (B : Fin (r + 1) → Over (Spec ↧ℂ)),
∃ inst20 : ∀ i, IsIntegral (B i).left,
    let := inst20
∃ inst21 : ∀ i, Smooth (B i).hom,
    let := inst21
∃ inst22 : ∀ i, IsProjective (B i).hom,
    let := inst22
∃ (e₀ : B 0 ≅ B₀),
∃ (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc),
∃ (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData),
∃ (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (z t)).comap e₀.hom.left),
∃ (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩)),
∃ (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U))),
∃ (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f), True := by
  obtain ⟨B, e₀, b, D, hD₀, hbase, _hcentres, hstep⟩ := hFamily
  refine ⟨B, (fun i => (hbase i).2.2), (fun i => (hbase i).1),
    (fun i => (hbase i).2.1), e₀, b, D, hD₀, ?_, ?_, ?_, True.intro⟩
  · intro i t
    exact (hstep i).1 t
  · intro i x
    exact (hstep i).2.1 x
  · intro i T f
    dsimp only
    intro hf
    exact (hstep i).2.2 T f hf

#print axioms g32t6_paired_base_native
end HodgeLean.Foundations.Program

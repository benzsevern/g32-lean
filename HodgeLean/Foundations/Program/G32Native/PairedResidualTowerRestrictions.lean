import HodgeLean.Foundations.Program.G32Native.PairedResidualAdaptedCoordinates
import HodgeLean.Foundations.Program.SchoenCycleS3LinksProofs
import HodgeLean.Foundations.Program.G32Native.PairedResidualIdealTransport

/-! # One adapted coordinate system for the actual retained tower -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The supplied tower preserves every unprocessed residue restriction in a single adapted scheme coordinate system. -/
theorem residual_tower_adapted_restrictions
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (b i).left).ideal U))
            ≃ₗ[Γ((B i.succ).left, U)] Γ((B i.succ).left, U)))
    (ℓ : ∀ i, Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B i)
    (htrans : ∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (hinit : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap (ℓ 0).left = residualCoefficientHyperplane M k r hd j ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap (ℓ 0).left = residualCoefficientHyperplane M k r hd j) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    ∃ (e : PP ≅ PP) (ι : Fin r ↪ Fin (k + 1)),
      ∀ (i : Fin (r + 1)) (j : Fin r), i.val ≤ j.val →
        (D i ⟨2 * j.val, by omega⟩).comap (e.hom ≫ ℓ i).left = s2e_s2b_residueIdeal k (ι j) ∧
        (D i ⟨2 * j.val + 1, by omega⟩).comap (e.hom ≫ ℓ i).left = s2e_s2b_residueIdeal k (ι j) := by
  dsimp only
  obtain ⟨e, ι, he⟩ := residual_coefficient_hyperplanes_adapted M k r hd
  have hzero (j : Fin r) :
      (D 0 ⟨2 * j.val, by omega⟩).comap (e.hom ≫ ℓ 0).left = s2e_s2b_residueIdeal k (ι j) ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap (e.hom ≫ ℓ 0).left = s2e_s2b_residueIdeal k (ι j) := by
    constructor
    · rw [Over.comp_left, Scheme.IdealSheafData.comap_comp, (hinit j).1, he j]
    · rw [Over.comp_left, Scheme.IdealSheafData.comap_comp, (hinit j).2, he j]
  refine ⟨e, ι, ?_⟩
  intro i j hij
  have h := s2e_chain_unprocessed_pair_transverse_aux k r i.val (by omega) ι
    (fun t : Fin (i.val + 1) => B ⟨t.val, by omega⟩)
    (fun t : Fin i.val => b ⟨t.val, by omega⟩)
    (fun t : Fin (i.val + 1) => D ⟨t.val, by omega⟩)
    (fun t s => htransform ⟨t.val, by omega⟩ s)
    (fun t => hcartier ⟨t.val, by omega⟩)
    (fun t => e.hom ≫ ℓ ⟨t.val, by omega⟩)
    (by
      intro t
      let p : Fin r := ⟨t.val, by omega⟩
      change (e.hom ≫ ℓ p.succ) ≫ b p = e.hom ≫ ℓ p.castSucc
      rw [Category.assoc, htrans])
    (by intro t; exact hzero t) j hij
  simpa only [Fin.val_last, Fin.eta] using h

/-- Every unprocessed branch restricts to its original actual residue ideal in the fixed supplied coordinates. -/
theorem residual_tower_unprocessed_restrictions
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (b i).left).ideal U))
            ≃ₗ[Γ((B i.succ).left, U)] Γ((B i.succ).left, U)))
    (ℓ : ∀ i, Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B i)
    (htrans : ∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (hinit : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap (ℓ 0).left = residualCoefficientHyperplane M k r hd j ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap (ℓ 0).left = residualCoefficientHyperplane M k r hd j) :
    ∀ (i : Fin (r + 1)) (j : Fin r), i.val ≤ j.val →
      (D i ⟨2 * j.val, by omega⟩).comap (ℓ i).left = residualCoefficientHyperplane M k r hd j ∧
      (D i ⟨2 * j.val + 1, by omega⟩).comap (ℓ i).left = residualCoefficientHyperplane M k r hd j := by
  obtain ⟨e, ι, hres⟩ := residual_tower_adapted_restrictions M k r hd B b D
    htransform hcartier ℓ htrans hinit
  intro i j hij
  have hH : (residualCoefficientHyperplane M k r hd j).comap e.hom.left =
      s2e_s2b_residueIdeal k (ι j) := by
    have h := (hres 0 j (by simp)).1
    rw [Over.comp_left, Scheme.IdealSheafData.comap_comp, (hinit j).1] at h
    exact h
  constructor
  · apply residual_ideal_comap_iso_injective ((Over.forget (Spec ↧ℂ)).mapIso e)
    change ((D i ⟨2 * j.val, by omega⟩).comap (ℓ i).left).comap e.hom.left =
      (residualCoefficientHyperplane M k r hd j).comap e.hom.left
    rw [← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, (hres i j hij).1, hH]
  · apply residual_ideal_comap_iso_injective ((Over.forget (Spec ↧ℂ)).mapIso e)
    change ((D i ⟨2 * j.val + 1, by omega⟩).comap (ℓ i).left).comap e.hom.left =
      (residualCoefficientHyperplane M k r hd j).comap e.hom.left
    rw [← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, (hres i j hij).2, hH]

/-- The actual exceptional centre ideal restricts to the specified residue hyperplane at its own tower step. -/
theorem residual_tower_exceptional_restriction
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1)
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (b i).left).ideal U))
            ≃ₗ[Γ((B i.succ).left, U)] Γ((B i.succ).left, U)))
    (ℓ : ∀ i, Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B i)
    (htrans : ∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (hinit : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap (ℓ 0).left = residualCoefficientHyperplane M k r hd j ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap (ℓ 0).left = residualCoefficientHyperplane M k r hd j) :
    ∀ i : Fin r,
      (((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
        (b i).left).comap (ℓ i.succ).left) = residualCoefficientHyperplane M k r hd i := by
  have hh := residual_tower_unprocessed_restrictions M k r hd B b D
    htransform hcartier ℓ htrans hinit
  intro i
  have hp := hh i.castSucc i (by rfl)
  have hf : (ℓ i.succ).left ≫ (b i).left = (ℓ i.castSucc).left :=
    congrArg Over.Hom.left (htrans i)
  rw [← Scheme.IdealSheafData.comap_comp, hf,
    Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]

#print axioms residual_tower_exceptional_restriction
#print axioms residual_tower_unprocessed_restrictions
#print axioms residual_tower_adapted_restrictions
end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.SchoenTransferR2ExceptionalFactor
import HodgeLean.Foundations.Program.SchoenTransferR2BranchCentre
import HodgeLean.Foundations.WitnessSelection.RetainedHelpers

/-! # Exceptional factorization for a retained normalization tower

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.WitnessSelection
namespace HodgeLean.Foundations.Program

/-- Loss of an initial branch along compatible component maps gives a factor
through one of the actual exceptional preimages to which primitive vanishing applies.
Source: Schoen (1988), Lemma 2.6, p. 18; Hartshorne, II.7.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_tower_exceptional_factor
    {K : Type} [Field K] {r : ℕ} (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsProjective (B i).hom]
    (η : ∀ i, Spec (CommRingCat.of K) ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (D : ∀ i, (B i).left.IdealSheafData)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hD : ∀ i : Fin r, D i.succ = s2c_strictTransform (b i).left (D i.castSucc) (I i))
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left]
    (f : ∀ i, Q ⟶ s2b_normalizationOver (B i) (η i))
    (hf : ∀ i : Fin r, f i.succ ≫ w i = f i.castSucc)
    [∀ i : Fin r, QuasiCompact
      (f i.succ ≫ s2b_normalizationMap (B i.succ) (η i.succ) ≫ b i).left]
    (hinit : (f 0 ≫ s2b_normalizationMap (B 0) (η 0)).left
      (genericPoint Q.left) ∈ (D 0).support)
    (hfinal : (f (Fin.last r) ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))).left
      (genericPoint Q.left) ∉ (D (Fin.last r)).support) :
    ∃ i : Fin r, ∃ ρ : Q ⟶ s2b_preimage
        (s2b_normalizationMap (B i.succ) (η i.succ))
        (pullback.fst (b i) (s2c_subschemeι (B i.castSucc) (I i))),
      ρ ≫ s2b_toCover (s2b_normalizationMap (B i.succ) (η i.succ))
        (pullback.fst (b i) (s2c_subschemeι (B i.castSucc) (I i))) = f i.succ := by
  have hbq (i : Fin r) :
      f i.succ ≫ s2b_normalizationMap (B i.succ) (η i.succ) ≫ b i =
        f i.castSucc ≫ s2b_normalizationMap (B i.castSucc) (η i.castSucc) := by
    rw [← normalization_transition_square _ _ _ _ (b i) (hη i) (w i) (hw i),
      ← Category.assoc, hf i]
  let x := fun i => (f i ≫ s2b_normalizationMap (B i) (η i)).left (genericPoint Q.left)
  have hx (i : Fin r) : (b i).left (x i.succ) = x i.castSucc :=
    congrArg (fun g : Q ⟶ B i.castSucc => g.left (genericPoint Q.left)) (hbq i)
  obtain ⟨i, hi⟩ := s4_assembly_branch_or_centre (fun i => (B i).left)
    (fun i => (b i).left) D I hD x hx hinit hfinal
  have hI : (f i.succ ≫ s2b_normalizationMap (B i.succ) (η i.succ) ≫ b i).left
      (genericPoint Q.left) ∈ (I i).support := by
    rw [hbq i]
    exact hi
  obtain ⟨ρ, hρ⟩ := s4_assembly_generic_exceptional_factor (b i) (I i)
    (s2b_normalizationMap (B i.succ) (η i.succ)) (f i.succ) hI
  exact ⟨i, ρ, hρ⟩

#print axioms s4_assembly_tower_exceptional_factor
end HodgeLean.Foundations.Program

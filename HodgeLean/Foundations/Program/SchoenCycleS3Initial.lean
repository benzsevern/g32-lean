import HodgeLean.Foundations.Program.SchoenCycleS3Coordinates
import HodgeLean.Foundations.Program.SchoenCycleS1c
import HodgeLean.Foundations.Program.SchoenCycleS3Links

/-! # Initial slice with adapted residue coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem s2e_symmetric_quotient_reindex
    (Z B : Over (Spec ↧ℂ)) (m n : ℕ) (hn : n = m)
    (γ : g3_power Z m ⟶ B)
    (hinv : ∀ τ, s2_permute Z m τ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z m ⟶ T),
      (∀ τ, s2_permute Z m τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f) :
    let γ' := eqToHom (congrArg (g3_power Z) hn) ≫ γ
    (∀ τ, s2_permute Z n τ ≫ γ' = γ') ∧
    Function.Surjective (Point.map γ') ∧
    (∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
      (∀ τ, s2_permute Z n τ ≫ f = f) → ∃! u : B ⟶ T, γ' ≫ u = f) := by
  subst n
  simpa only [eqToHom_refl, Category.id_comp] using And.intro hinv (And.intro hsurj hquot)

theorem s2e_initial_slice_coordinate_restrictions
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hg : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ τ, s2_permute Z (2 * k) τ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (2 * k) ⟶ T),
      (∀ τ, s2_permute Z (2 * k) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (hpair : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0)
    (n : ℕ) (hn : 2 * k = n + 1) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let γn := eqToHom (congrArg (g3_power Z) hn.symm) ≫ γ
    ∃ (ι : Fin r ↪ Fin (k + 1)) (ℓ : PP ⟶ B),
      IsClosedImmersion ℓ.left ∧ ∀ j : Fin r,
        (s2c_branchIdeal Z B n γn (y ⟨2 * j.val, by omega⟩)).comap ℓ.left =
          s2e_s2b_residueIdeal k (ι j) ∧
        (s2c_branchIdeal Z B n γn (y ⟨2 * j.val + 1, by omega⟩)).comap ℓ.left =
          s2e_s2b_residueIdeal k (ι j) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  obtain ⟨ℓ, hℓ⟩ := s2e_chain_paired_divisor_morphism Z B k r hr y hy w hres horder hout
    hg hd γ hγ
  have hclosed := s2e_chain_paired_immersion Z B k r hr y hy w hres horder hout
    hg hd γ hγ hsurj hquot ℓ hℓ
  obtain ⟨b, ι, hb⟩ := s2e_residue_adapted_coefficients
    (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) k r hd
  obtain ⟨e, he⟩ := s2e_chain_adapted_residue_ideals
    (Fin 1 → ℂ) (ComplexPoint Z) k r hd b ι hb
  refine ⟨ι, e.hom ≫ ℓ, ?_, ?_⟩
  · haveI := hclosed
    change IsClosedImmersion (e.hom.left ≫ ℓ.left)
    infer_instance
  · intro j
    obtain ⟨h₁, h₂⟩ := s2e_chain_paired_branch_ideals Z B k r hr y hy w hres horder hout
      hg hd γ hγ hsurj hquot ℓ hℓ hpair n hn j
    change _ = _ ∧ _ = _
    rw [Over.comp_left, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, h₁, h₂]
    exact ⟨he j, he j⟩

end HodgeLean.Foundations.Program

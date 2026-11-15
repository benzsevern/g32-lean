import HodgeLean.Foundations.RepFoundationsDeterminant

/-! # Representation foundations: determinants on eigenspaces of a subgroup

The averaging projector onto `W^{H, χ}`, and the determinant of a centralizer element on
`V^{H, χ}` through the isotypic decomposition `V^{H, χ} ≅ ⊕_i σ_i^{H, χ} ⊗ M_{σ_i}`.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G] [Fintype G]

section Proj

variable {W : Type} [AddCommGroup W] [Module ℂ W]

open scoped Classical in
/-- The averaging projector `|H|⁻¹ Σ_h χ(h)⁻¹ ρ(h)` onto `W^{H, χ}`. -/
def rfd_eigenProj (ρ : Representation ℂ G W) (H : Subgroup G) (χ : H →* ℂˣ) :
    Module.End ℂ W :=
  (Fintype.card H : ℂ)⁻¹ • ∑ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) • ρ h

open scoped Classical in
theorem rfd_eigenProj_apply (ρ : Representation ℂ G W) (H : Subgroup G) (χ : H →* ℂˣ)
    (v : W) :
    rfd_eigenProj ρ H χ v = (Fintype.card H : ℂ)⁻¹ • ∑ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) • ρ h v := by
  simp [rfd_eigenProj, LinearMap.sum_apply]

theorem rfd_eigenProj_mem (ρ : Representation ℂ G W) (H : Subgroup G) (χ : H →* ℂˣ)
    (v : W) : rfd_eigenProj ρ H χ v ∈ rfd_eigen ρ H χ := by
  classical
  intro k
  rw [rfd_eigenProj_apply, map_smul, map_sum, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ fun h => ?_
  simp only [Equiv.coe_mulLeft, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply,
    mul_inv_rev, Units.val_mul, smul_smul]
  congr 1
  rw [mul_comm, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem rfd_eigenProj_of_mem (ρ : Representation ℂ G W) (H : Subgroup G) (χ : H →* ℂˣ)
    {v : W} (hv : v ∈ rfd_eigen ρ H χ) : rfd_eigenProj ρ H χ v = v := by
  classical
  rw [rfd_eigenProj_apply]
  have : ∀ h : H, (((χ h)⁻¹ : ℂˣ) : ℂ) • ρ h v = v := fun h => by
    rw [hv h, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by simp), one_smul]

/-- An intertwining map commutes with the averaging projectors. -/
theorem rfd_eigenProj_comm {X : Type} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X) (ρ : Representation ℂ G W) (H : Subgroup G) (χ : H →* ℂˣ)
    (φ : X →ₗ[ℂ] W) (hφ : ∀ g, φ ∘ₗ π g = ρ g ∘ₗ φ) (x : X) :
    φ (rfd_eigenProj π H χ x) = rfd_eigenProj ρ H χ (φ x) := by
  classical
  rw [rfd_eigenProj_apply, rfd_eigenProj_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul]
  exact congrArg _ (LinearMap.congr_fun (hφ h) x)

end Proj

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The inclusion `⊕_i σ_i^{H, χ} ⊗ M_{σ_i} → ⊕_i σ_i ⊗ M_{σ_i}`. -/
def rfd_eigenIncl {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    (∀ i, rfd_eigen (σ i).ρ H χ ⊗[ℂ] rfd_mult (σ i) ρ) →ₗ[ℂ]
      (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) :=
  LinearMap.pi fun i => TensorProduct.map (rfd_eigen (σ i).ρ H χ).subtype LinearMap.id ∘ₗ
    LinearMap.proj i

/-- The projection `⊕_i σ_i ⊗ M_{σ_i} → ⊕_i σ_i^{H, χ} ⊗ M_{σ_i}`. -/
def rfd_eigenPr {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) →ₗ[ℂ]
      (∀ i, rfd_eigen (σ i).ρ H χ ⊗[ℂ] rfd_mult (σ i) ρ) :=
  LinearMap.pi fun i => TensorProduct.map
    ((rfd_eigenProj (σ i).ρ H χ).codRestrict _ (rfd_eigenProj_mem _ H χ)) LinearMap.id ∘ₗ
    LinearMap.proj i

omit [FiniteDimensional ℂ V] in
theorem rfd_eval_eigenIncl_eigenPr {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (H : Subgroup G) (χ : H →* ℂˣ) :
    rfd_eval σ ρ ∘ₗ rfd_eigenIncl σ ρ H χ ∘ₗ rfd_eigenPr σ ρ H χ =
      rfd_eigenProj ρ H χ ∘ₗ rfd_eval σ ρ := by
  classical
  refine LinearMap.pi_ext' fun i => TensorProduct.ext' fun x φ => ?_
  have h1 : (rfd_eigenIncl σ ρ H χ ∘ₗ rfd_eigenPr σ ρ H χ) (Pi.single i (x ⊗ₜ φ)) =
      Pi.single i (rfd_eigenProj (σ i).ρ H χ x ⊗ₜ φ) := by
    funext j
    by_cases h : j = i
    · subst h; simp [rfd_eigenIncl, rfd_eigenPr]
    · simp [rfd_eigenIncl, rfd_eigenPr, Pi.single_eq_of_ne h]
  simp only [LinearMap.comp_apply] at h1
  simp only [LinearMap.comp_apply, LinearMap.single_apply]
  rw [h1, rfd_eval_single_tmul, rfd_eval_single_tmul]
  exact rfd_eigenProj_comm _ ρ H χ φ.1 φ.2 x

/-- The evaluation map `⊕_i σ_i^{H, χ} ⊗ M_{σ_i} → V^{H, χ}`. -/
def rfd_eigenEval {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    (∀ i, rfd_eigen (σ i).ρ H χ ⊗[ℂ] rfd_mult (σ i) ρ) →ₗ[ℂ] rfd_eigen ρ H χ :=
  (rfd_eval σ ρ ∘ₗ rfd_eigenIncl σ ρ H χ).codRestrict _ fun s => by
    classical
    have h : rfd_eigenIncl σ ρ H χ s =
        rfd_eigenIncl σ ρ H χ (rfd_eigenPr σ ρ H χ (rfd_eigenIncl σ ρ H χ s)) := by
      funext i
      have hid : TensorProduct.map ((rfd_eigenProj (σ i).ρ H χ).codRestrict _
          (rfd_eigenProj_mem _ H χ)) (LinearMap.id : rfd_mult (σ i) ρ →ₗ[ℂ] _) ∘ₗ
          TensorProduct.map (rfd_eigen (σ i).ρ H χ).subtype LinearMap.id = LinearMap.id := by
        refine TensorProduct.ext' fun x φ => ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
        congr 1
        exact Subtype.ext (rfd_eigenProj_of_mem _ H χ x.2)
      simp only [rfd_eigenIncl, rfd_eigenPr, LinearMap.pi_apply, LinearMap.comp_apply,
        LinearMap.proj_apply]
      exact congrArg _ (LinearMap.congr_fun hid (s i)).symm
    have h2 := LinearMap.congr_fun (rfd_eval_eigenIncl_eigenPr σ ρ H χ)
      (rfd_eigenIncl σ ρ H χ s)
    simp only [LinearMap.comp_apply] at h2 ⊢
    rw [h, h2]
    exact rfd_eigenProj_mem _ H χ _

theorem rfd_eigenEval_bijective {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (H : Subgroup G) (χ : H →* ℂˣ) :
    Function.Bijective (rfd_eigenEval σ ρ H χ) := by
  have hb := rfd_eval_bijective' σ ρ hσ hdist hcov
  constructor
  · intro s t hst
    have h1 : rfd_eval σ ρ (rfd_eigenIncl σ ρ H χ s) = rfd_eval σ ρ (rfd_eigenIncl σ ρ H χ t) :=
      congrArg Subtype.val hst
    have h2 := hb.1 h1
    funext i
    have h3 := congrFun h2 i
    simp only [rfd_eigenIncl, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.proj_apply] at h3
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective h3
  · intro v
    obtain ⟨s, hs⟩ := hb.2 v.1
    refine ⟨rfd_eigenPr σ ρ H χ s, Subtype.ext ?_⟩
    change (rfd_eval σ ρ ∘ₗ rfd_eigenIncl σ ρ H χ ∘ₗ rfd_eigenPr σ ρ H χ) s = v.1
    rw [rfd_eval_eigenIncl_eigenPr, LinearMap.comp_apply, hs]
    exact rfd_eigenProj_of_mem _ H χ v.2

theorem rfd_det_eigen' {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (H : Subgroup G) (χ : H →* ℂˣ)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det (rfd_eigenAct ρ H χ u hu) =
      ∏ i, rfd_det (σ i) ρ u hu ^ Module.finrank ℂ (rfd_eigen (σ i).ρ H χ) := by
  let e := LinearEquiv.ofBijective _ (rfd_eigenEval_bijective σ ρ hσ hdist hcov H χ)
  let A : Module.End ℂ (∀ i, rfd_eigen (σ i).ρ H χ ⊗[ℂ] rfd_mult (σ i) ρ) :=
    LinearMap.pi fun i => TensorProduct.map LinearMap.id (rfd_multAct (σ i) ρ u hu) ∘ₗ
      LinearMap.proj i
  have hA : rfd_eigenIncl σ ρ H χ ∘ₗ A = rfd_evalAct σ ρ u hu ∘ₗ rfd_eigenIncl σ ρ H χ := by
    classical
    refine LinearMap.pi_ext' fun i => TensorProduct.ext' fun x φ => ?_
    funext j
    by_cases h : j = i
    · subst h; simp [A, rfd_eigenIncl, rfd_evalAct]
    · simp [A, rfd_eigenIncl, rfd_evalAct, Pi.single_eq_of_ne h]
  have h : rfd_eigenAct ρ H χ u hu =
      (e : _ →ₗ[ℂ] rfd_eigen ρ H χ) ∘ₗ A ∘ₗ (e.symm : rfd_eigen ρ H χ →ₗ[ℂ] _) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨s, rfl⟩ := e.surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    refine Subtype.ext ?_
    change u (rfd_eval σ ρ (rfd_eigenIncl σ ρ H χ s)) =
      rfd_eval σ ρ (rfd_eigenIncl σ ρ H χ (A s))
    have h2 := LinearMap.congr_fun hA s
    have h3 := LinearMap.congr_fun (rfd_eval_comp_evalAct σ ρ u hu) (rfd_eigenIncl σ ρ H χ s)
    simp only [LinearMap.comp_apply] at h2 h3
    rw [h2, h3]
  rw [h, LinearMap.det_conj, rfd_det_pi]
  exact Finset.prod_congr rfl fun i _ => rfd_det_map_id _

end HodgeLean.Foundations

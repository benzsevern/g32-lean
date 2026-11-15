import HodgeLean.Foundations.RepFoundationsIsotypic

/-! # Representation foundations: determinants of centralizer elements

The determinant of a centralizer element on `V` and on the eigenspaces `V^{H, χ}`, computed
through the isotypic decomposition.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped TensorProduct

/-- The determinant of a block-diagonal endomorphism of a finite product of spaces. -/
theorem rfd_det_pi {ι : Type} [Fintype ι] (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] [∀ i, FiniteDimensional ℂ (M i)] (f : ∀ i, Module.End ℂ (M i)) :
    LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∏ i, LinearMap.det (f i) := by
  revert M
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, FiniteDimensional ℂ (M i)]
    (f : ∀ i, Module.End ℂ (M i)),
    LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∏ i, LinearMap.det (f i))
    ?_ ?_ ?_ ι
  · intro α β _ e h M _ _ _ f
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    let F : (∀ b, M b) ≃ₗ[ℂ] (∀ a, M (e a)) := LinearEquiv.piCongrLeft' ℂ M e.symm
    have h1 := h (fun a => M (e a)) (fun a => f (e a))
    have h2 : (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
        (F.symm : _ →ₗ[ℂ] _) ∘ₗ (LinearMap.pi fun a => f (e a) ∘ₗ LinearMap.proj a) ∘ₗ
          (F.symm.symm : _ →ₗ[ℂ] _) := by
      refine LinearMap.ext fun x => F.injective ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
        LinearEquiv.apply_symm_apply]
      rfl
    rw [h2, LinearMap.det_conj, h1]
    exact Fintype.prod_equiv e _ _ fun _ => rfl
  · intro M _ _ _ f
    rw [LinearMap.det_eq_one_of_subsingleton]
    simp
  · intro α _ h M _ _ _ f
    let E := (LinearEquiv.piOptionEquivProd (R := ℂ) (M := M)).symm
    have h1 := h (fun a => M (some a)) (fun a => f (some a))
    have h2 : (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
        (E : _ →ₗ[ℂ] _) ∘ₗ (LinearMap.prodMap (f none)
          (LinearMap.pi fun a => f (some a) ∘ₗ LinearMap.proj a)) ∘ₗ (E.symm : _ →ₗ[ℂ] _) := by
      ext x o
      cases o <;> rfl
    rw [h2, LinearMap.det_conj, LinearMap.det_prodMap, h1, Fintype.prod_option]

/-- `det(1_X ⊗ A) = det(A)^{dim X}`. -/
theorem rfd_det_map_id {X M : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (A : Module.End ℂ M) :
    LinearMap.det (TensorProduct.map (LinearMap.id : X →ₗ[ℂ] X) A) =
      LinearMap.det A ^ Module.finrank ℂ X := by
  let bX := Module.finBasis ℂ X
  let bM := Module.finBasis ℂ M
  rw [← LinearMap.det_toMatrix (bX.tensorProduct bM), TensorProduct.toMatrix_map,
    LinearMap.toMatrix_id, Matrix.det_kronecker, ← LinearMap.det_toMatrix bM]
  simp

variable {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

theorem rfd_det_eq_prod' {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det u = ∏ i, rfd_det (σ i) ρ u hu ^ Module.finrank ℂ (σ i) := by
  let e := LinearEquiv.ofBijective _ (rfd_eval_bijective' σ ρ hσ hdist hcov)
  have h : u = (e : _ →ₗ[ℂ] V) ∘ₗ rfd_evalAct σ ρ u hu ∘ₗ (e.symm : V →ₗ[ℂ] _) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨s, rfl⟩ := e.surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (LinearMap.congr_fun (rfd_eval_comp_evalAct σ ρ u hu) s).symm
  calc LinearMap.det u
      = LinearMap.det ((e : _ →ₗ[ℂ] V) ∘ₗ rfd_evalAct σ ρ u hu ∘ₗ (e.symm : V →ₗ[ℂ] _)) :=
        congrArg _ h
    _ = _ := by
        rw [LinearMap.det_conj, rfd_evalAct, rfd_det_pi]
        exact Finset.prod_congr rfl fun i _ => rfd_det_map_id _

end HodgeLean.Foundations

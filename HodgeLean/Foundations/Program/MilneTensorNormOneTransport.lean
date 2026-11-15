import HodgeLean.Foundations.Program.MilneTensorTransport

noncomputable section
namespace HodgeLean.Foundations.Program

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_norm_one_image_conj
    (A : Subalgebra ℂ (Module.End ℂ V))
    {R : Type*} [Ring R] [Algebra ℂ R]
    (e : A ≃ₐ[ℂ] R) (E : V ≃ₗ[ℂ] W) (ρ : R →ₐ[ℂ] Module.End ℂ W)
    (τ : A ≃ₗ[ℂ] A) (σ : R ≃ₗ[ℂ] R)
    (hτσ : ∀ a, σ (e a) = e (τ a))
    (hE : ∀ (a : A) (v : V), E ((a : Module.End ℂ V) v) = ρ (e a) (E v)) :
    E.conj '' {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1} =
      {u | ∃ b : R, ρ b = u ∧ σ b * b = 1} := by
  have hconj (a : A) : E.conj (a : Module.End ℂ V) = ρ (e a) := by
    ext w
    simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply] using
      hE a (E.symm w)
  ext u
  constructor
  · rintro ⟨v, ⟨a, rfl, ha⟩, rfl⟩
    refine ⟨e a, (hconj a).symm, ?_⟩
    rw [hτσ, ← map_mul, ha, map_one]
  · rintro ⟨b, rfl, hb⟩
    refine ⟨(e.symm b : Module.End ℂ V), ⟨e.symm b, rfl, ?_⟩, ?_⟩
    · apply e.injective
      rw [map_mul, map_one, ← hτσ, e.apply_symm_apply]
      exact hb
    · rw [hconj, e.apply_symm_apply]

theorem m1b_copies_conj_image (E : V ≃ₗ[ℂ] W)
    (S : Set (Module.End ℂ V)) (r : ℕ) :
    (m1b_copiesEquiv E r).conj '' (m1b_copies r '' S) =
      m1b_copies r '' (E.conj '' S) := by
  rw [Set.image_image, Set.image_image]
  congr 1

theorem m1b_involution_one {R : Type*} [Ring R] [Algebra ℂ R]
    (τ : R ≃ₗ[ℂ] R) (hmul : ∀ a b, τ (a * b) = τ b * τ a) : τ 1 = 1 := by
  have h := hmul (τ.symm 1) 1
  simpa only [mul_one, τ.apply_symm_apply] using h.symm

theorem m1b_norm_one_neg_one (A : Subalgebra ℂ (Module.End ℂ V))
    (τ : A ≃ₗ[ℂ] A) (hmul : ∀ a b, τ (a * b) = τ b * τ a) :
    (-1 : Module.End ℂ V) ∈
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1} := by
  refine ⟨-1, rfl, ?_⟩
  have hneg : τ (-1 : A) = -1 :=
    (τ.toLinearMap.map_neg (1 : A)).trans
      (congrArg Neg.neg (m1b_involution_one τ hmul))
  calc τ (-1) * (-1) = (-1 : A) * (-1) := congrArg (fun z : A => z * (-1)) hneg
       _ = 1 := by rw [neg_mul_neg, one_mul]

end HodgeLean.Foundations.Program

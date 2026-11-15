import HodgeLean.Foundations.Program.PeriodMarkingComparison
import HodgeLean.Foundations.Program.ParabolicCohomologyRoot

noncomputable section
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem b64b_eigenspace_affine_pullback {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    (A : Module.End ℂ V) (Z : Module.End ℂ W) (I : V →ₗ[ℂ] W)
    (hI : Function.Injective I)
    (hA : ∀ x, I (A x) = I x + (2 : ℂ) • Z (I x)) (z : ℂ) :
    Module.End.eigenspace A (1 + 2 * z) = (Module.End.eigenspace Z z).comap I := by
  apply Submodule.ext
  intro x
  simp only [Submodule.mem_comap, Module.End.mem_eigenspace_iff]
  constructor
  · intro hx
    have hh : (2 : ℂ) • Z (I x) = (2 : ℂ) • (z • I x) := by
      apply add_left_cancel (a := I x)
      calc
        I x + (2 : ℂ) • Z (I x) = I (A x) := (hA x).symm
        _ = (1 + 2 * z) • I x := by rw [hx, map_smul]
        _ = I x + (2 : ℂ) • (z • I x) := by rw [add_smul, one_smul, mul_smul]
    have hz : (2 : ℂ) • (Z (I x) - z • I x) = 0 := by rw [smul_sub, hh, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro hx
    apply hI
    rw [hA, map_smul, hx, add_smul, one_smul, mul_smul]

theorem b64b_root_eigenvalue :
    1 + 2 * HodgeLean.Papers.g32h_omega = Complex.I * (Real.sqrt 3 : ℂ) := by
  have hom : hp_embed QuadraticAlgebra.omega = Complex.I * (Real.sqrt 3 : ℂ) := by
    simp [hp_embed]
  have hz : hp_embed pc_zeta = (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2 := by
    rw [pc_zeta, map_div₀, map_add, map_neg, map_one, hom, map_ofNat]
  rw [← hp_embed_zeta_eq, hz]
  ring

theorem b64b_conjugate_root_eigenvalue :
    1 + 2 * star HodgeLean.Papers.g32h_omega = -Complex.I * (Real.sqrt 3 : ℂ) := by
  simpa using congrArg star b64b_root_eigenvalue

theorem b64b_period_operator_complex (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    {M : Type*} [AddCommGroup M]
    (i : M →ₗ[ℤ] b3_periodLattice ℂ C) (A : M →ₗ[ℤ] M)
    (hA : ∀ x, i (A x) = b63d_periodOperator C hG (i x))
    (x : ℂ ⊗[ℤ] M) :
    i.baseChange ℂ (A.baseChange ℂ x) = i.baseChange ℂ x +
      (2 : ℂ) • (b4b_centreAct C hG).toIntLinearMap.baseChange ℂ (i.baseChange ℂ x) := by
  have hi (x : M) : i (A x) = i x +
      (b4b_centreAct C hG) (i x) + (b4b_centreAct C hG) (i x) := by
    simpa only [b63d_periodOperator, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, two_smul, add_assoc, AddMonoidHom.coe_toIntLinearMap] using hA x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | tmul c x =>
    simpa only [LinearMap.baseChange_tmul, two_smul, TensorProduct.tmul_add, add_assoc, AddMonoidHom.coe_toIntLinearMap]
      using congrArg (fun z => c ⊗ₜ[ℤ] z) (hi x)

theorem b64b_period_eigen_rank (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    {M : Type*} [AddCommGroup M]
    (e : M ≃ₗ[ℤ] b63l_periodLattice C) (A : M →ₗ[ℤ] M)
    (hA : ∀ x, (e (A x)).val = b63d_periodOperator C hG (e x).val) (z : ℂ) :
    Module.finrank ℂ ↥((b63l_periodF C).comap (e.baseChange ℤ ℂ _ _).toLinearMap ⊓
      Module.End.eigenspace (A.baseChange ℂ) (1 + 2 * z)) =
      Module.finrank ℂ (b63d_eigenF C hG z) := by
  let eC := e.baseChange ℤ ℂ M (b63l_periodLattice C)
  let j := (b63l_periodLattice C).subtype
  let i := j.comp e.toLinearMap
  have hi : Function.Injective (i.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap i
      ((b63l_periodLattice C).subtype_injective.comp e.injective)
  have hcompat := b64b_period_operator_complex C hG i A hA
  have heC : i.baseChange ℂ = (j.baseChange ℂ).comp eC.toLinearMap := by
    change (j.comp e.toLinearMap).baseChange ℂ = _
    rw [LinearMap.baseChange_comp]
    rfl
  have heig : (b63l_periodF C).comap eC.toLinearMap ⊓
      Module.End.eigenspace (A.baseChange ℂ) (1 + 2 * z) =
      (b63d_eigenF C hG z).comap eC.toLinearMap := by
    rw [b64b_eigenspace_affine_pullback _ _ _ hi hcompat]
    apply Submodule.ext
    intro x
    simp only [Submodule.mem_inf, Submodule.mem_comap, Module.End.mem_eigenspace_iff,
      b63d_eigenF, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, heC, LinearMap.comp_apply, sub_eq_zero, j]
  change Module.finrank ℂ ↥((b63l_periodF C).comap eC.toLinearMap ⊓ _) = _
  rw [heig]
  exact (Submodule.comap_equiv_self_of_inj_of_le (p := b63d_eigenF C hG z)
    eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq

end HodgeLean.Foundations.Program

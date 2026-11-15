import HodgeLean.Foundations.Program.MilneScalarPoints

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem m2_transport_invariant_images {K V W Y ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Y] [Module K Y] (e : V ≃ₗ[K] W)
    (a : ι → Module.End K V) (c : ι → Module.End K W)
    (f : W →ₗ[K] Y) (g : V →ₗ[K] Y)
    (ha : ∀ i, c i ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ a i)
    (hf : f ∘ₗ e.toLinearMap = g) :
    (⨅ i, LinearMap.eqLocus (c i) LinearMap.id).map f =
      (⨅ i, LinearMap.eqLocus (a i) LinearMap.id).map g := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨e.symm w, (Submodule.mem_iInf _).mpr (fun i => ?_), ?_⟩
    · apply e.injective
      have h := LinearMap.congr_fun (ha i) (e.symm w)
      have hw' : c i w = w := (Submodule.mem_iInf _).mp hw i
      simpa only [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, hw'] using h.symm
    · exact (LinearMap.congr_fun hf (e.symm w)).symm.trans
        (congrArg f (e.apply_symm_apply w))
  · rintro ⟨v, hv, rfl⟩
    refine ⟨e v, (Submodule.mem_iInf _).mpr (fun i => ?_), LinearMap.congr_fun hf v⟩
    have hv' : a i v = v := (Submodule.mem_iInf _).mp hv i
    have h := LinearMap.congr_fun (ha i) v
    simpa only [LinearMap.mem_eqLocus, LinearMap.id_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hv'] using h


theorem m2_polynomial_invariant_images_descend {K A L V W Y ι : Type*}
    [Field K] [PerfectField K] [CommRing A] [Algebra K A] [IsReduced A]
    [Algebra.FiniteType K A] [Field L] [IsAlgClosed L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    [AddCommGroup Y] [Module K Y] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (M : Matrix ι ι A) (g : V →ₗ[K] Y)
    (e : L ⊗[K] V ≃ₗ[L] W) (c : (A →ₐ[K] L) → Module.End L W)
    (f : W →ₗ[L] L ⊗[K] Y)
    (ha : ∀ φ, c φ ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ
      Matrix.toLin (b.baseChange L) (b.baseChange L) (M.map φ))
    (hf : f ∘ₗ e.toLinearMap = g.baseChange L) :
    (⨅ φ, LinearMap.eqLocus (c φ) LinearMap.id).map f =
      ((((⨅ φ, LinearMap.eqLocus (c φ) LinearMap.id).map f).restrictScalars K).comap
        (TensorProduct.mk K L Y 1)).baseChange L := by
  have hs := m2_transport_invariant_images e
    (fun φ : A →ₐ[K] L => Matrix.toLin (b.baseChange L) (b.baseChange L) (M.map φ)) c
      f (g.baseChange L) ha hf
  rw [hs]
  exact m2_matrix_invariant_images_descend (L := L) b M g


end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.MilneTensorScalar

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def m1b_tensorEquiv (e : V ≃ₗ[ℂ] W) (n : ℕ) : (⨂[ℂ]^n V) ≃ₗ[ℂ] (⨂[ℂ]^n W) :=
  PiTensorProduct.congr (fun _ : Fin n => e)

theorem m1b_tensorEquiv_perm (e : V ≃ₗ[ℂ] W) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (t : ⨂[ℂ]^n V) :
    m1b_tensorEquiv e n (SchurWeyl.permRep ℂ V (Fin n) σ t) =
      SchurWeyl.permRep ℂ W (Fin n) σ (m1b_tensorEquiv e n t) := by
  have h : (m1b_tensorEquiv e n).toLinearMap.comp
      (SchurWeyl.permRep ℂ V (Fin n) σ) =
      (SchurWeyl.permRep ℂ W (Fin n) σ).comp (m1b_tensorEquiv e n).toLinearMap := by
    ext v
    simp [m1b_tensorEquiv, SchurWeyl.permRep_tprod]
  exact LinearMap.congr_fun h t

theorem m1b_tensorEquiv_append (e : V ≃ₗ[ℂ] W) (k l : ℕ)
    (a : ⨂[ℂ]^k V) (b : ⨂[ℂ]^l V) :
    m1b_tensorEquiv e (k + l) (InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b)) =
      InvariantsExterior.tensorAppend k l
        (m1b_tensorEquiv e k a ⊗ₜ[ℂ] m1b_tensorEquiv e l b) := by
  have h : (m1b_tensorEquiv e (k + l)).toLinearMap.comp
      (InvariantsExterior.tensorAppend k l).toLinearMap =
      (InvariantsExterior.tensorAppend k l).toLinearMap.comp
        (TensorProduct.map (m1b_tensorEquiv e k).toLinearMap (m1b_tensorEquiv e l).toLinearMap) := by
    ext x y
    change m1b_tensorEquiv e (k + l)
      (InvariantsExterior.tensorAppend k l
        (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
      InvariantsExterior.tensorAppend k l
        (TensorProduct.map (m1b_tensorEquiv e k).toLinearMap (m1b_tensorEquiv e l).toLinearMap
          (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y))
    simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      InvariantsExterior.tensorAppend_tprod, m1b_tensorEquiv, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  exact LinearMap.congr_fun h (a ⊗ₜ[ℂ] b)

theorem m1b_products_transport (e : V ≃ₗ[ℂ] W)
    (Q : Submodule ℂ (⨂[ℂ]^2 V)) : ∀ (n : ℕ) (t : ⨂[ℂ]^n V),
    t ∈ m1b_products Q n → m1b_tensorEquiv e n t ∈
      m1b_products (Q.map (m1b_tensorEquiv e 2).toLinearMap) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro t _; exact Submodule.mem_top
  | one =>
    intro t ht
    have ht' : t = 0 := ht
    rw [ht', map_zero]
    exact Submodule.zero_mem _
  | more n ih _ =>
    intro t ht
    rw [m1b_products] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨σ, a, b, ha, hb, rfl⟩ := ht
      rw [m1b_tensorEquiv_perm, m1b_tensorEquiv_append]
      apply Submodule.subset_span
      exact ⟨σ, m1b_tensorEquiv e n a, m1b_tensorEquiv e 2 b,
        ih a ha, ⟨b, hb, rfl⟩, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ihx

theorem m1b_tensorEquiv_symm (e : V ≃ₗ[ℂ] W) (n : ℕ) :
    m1b_tensorEquiv e.symm n = (m1b_tensorEquiv e n).symm := by
  apply LinearEquiv.toLinearMap_injective
  rfl

theorem m1b_products_map (e : V ≃ₗ[ℂ] W)
    (Q : Submodule ℂ (⨂[ℂ]^2 V)) (n : ℕ) :
    (m1b_products Q n).map (m1b_tensorEquiv e n).toLinearMap =
      m1b_products (Q.map (m1b_tensorEquiv e 2).toLinearMap) n := by
  apply le_antisymm
  · rintro w ⟨t, ht, rfl⟩
    exact m1b_products_transport e Q n t ht
  · intro w hw
    refine ⟨(m1b_tensorEquiv e n).symm w, ?_, (m1b_tensorEquiv e n).apply_symm_apply w⟩
    have h := m1b_products_transport e.symm (Q.map (m1b_tensorEquiv e 2).toLinearMap) n w hw
    rw [m1b_tensorEquiv_symm, m1b_tensorEquiv_symm, ← Submodule.map_comp] at h
    have hc : (m1b_tensorEquiv e 2).symm.toLinearMap.comp
        (m1b_tensorEquiv e 2).toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hc, Submodule.map_id] at h
    exact h

theorem m1b_tensorEquiv_action (e : V ≃ₗ[ℂ] W)
    (u : Module.End ℂ V) (n : ℕ) (t : ⨂[ℂ]^n V) :
    m1b_tensorEquiv e n (SchurWeyl.tensorPow (Fin n) u t) =
      SchurWeyl.tensorPow (Fin n) (e.conj u) (m1b_tensorEquiv e n t) := by
  have h : (m1b_tensorEquiv e n).toLinearMap.comp (SchurWeyl.tensorPow (Fin n) u) =
      (SchurWeyl.tensorPow (Fin n) (e.conj u)).comp (m1b_tensorEquiv e n).toLinearMap := by
    ext v
    simp [m1b_tensorEquiv]
  exact LinearMap.congr_fun h t

theorem m1b_fixed_transport (e : V ≃ₗ[ℂ] W)
    (S : Set (Module.End ℂ V)) (n : ℕ) (t : ⨂[ℂ]^n V) :
    m1b_tensorEquiv e n t ∈ m1b_fixed (e.conj '' S) n ↔ t ∈ m1b_fixed S n := by
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h u hu
    apply (m1b_tensorEquiv e n).injective
    rw [m1b_tensorEquiv_action]
    exact h (e.conj u) ⟨u, hu, rfl⟩
  · intro h v hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← m1b_tensorEquiv_action, h u hu]

theorem m1b_fixed_map (e : V ≃ₗ[ℂ] W) (S : Set (Module.End ℂ V)) (n : ℕ) :
    (m1b_fixed S n).map (m1b_tensorEquiv e n).toLinearMap =
      m1b_fixed (e.conj '' S) n := by
  apply le_antisymm
  · rintro w ⟨t, ht, rfl⟩
    exact (m1b_fixed_transport e S n t).mpr ht
  · intro w hw
    refine ⟨(m1b_tensorEquiv e n).symm w, ?_, (m1b_tensorEquiv e n).apply_symm_apply w⟩
    apply (m1b_fixed_transport e S n _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hw

theorem m1b_generation_conj_iff (e : V ≃ₗ[ℂ] W)
    (S : Set (Module.End ℂ V)) (n : ℕ) :
    m1b_fixed S n = m1b_products (m1b_fixed S 2) n ↔
      m1b_fixed (e.conj '' S) n = m1b_products (m1b_fixed (e.conj '' S) 2) n := by
  constructor
  · intro h
    have hc := congrArg (fun P : Submodule ℂ (⨂[ℂ]^n V) =>
      P.map (m1b_tensorEquiv e n).toLinearMap) h
    rwa [m1b_fixed_map, m1b_products_map, m1b_fixed_map] at hc
  · intro h
    apply Submodule.map_injective_of_injective (m1b_tensorEquiv e n).injective
    rw [m1b_fixed_map, m1b_products_map, m1b_fixed_map]
    exact h

theorem m1b_isometries_conj (e : V ≃ₗ[ℂ] W) (B : LinearMap.BilinForm ℂ V) :
    e.conj '' m1b_isometries B =
      m1b_isometries (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨hu.1.map (e.conjAlgEquiv ℂ).toMonoidHom, ?_⟩
    intro x y
    simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply] using hu.2 (e.symm x) (e.symm y)
  · intro hv
    refine ⟨e.symm.conj v, ⟨hv.1.map (e.symm.conjAlgEquiv ℂ).toMonoidHom, ?_⟩, ?_⟩
    · intro x y
      simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.conj_apply_apply,
        LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply] using hv.2 (e x) (e y)
    · ext x
      simp

def m1b_copiesEquiv (e : V ≃ₗ[ℂ] W) (r : ℕ) :
    (Fin r → V) ≃ₗ[ℂ] (Fin r → W) :=
  LinearEquiv.piCongrRight (fun _ : Fin r => e)

theorem m1b_copiesEquiv_conj (e : V ≃ₗ[ℂ] W) (r : ℕ) (u : Module.End ℂ V) :
    (m1b_copiesEquiv e r).conj (m1b_copies r u) = m1b_copies r (e.conj u) := by
  ext x i
  rfl

theorem m1b_copies_isometries_conj (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) (r : ℕ) :
    (m1b_copiesEquiv e r).conj '' (m1b_copies r '' m1b_isometries B) =
      m1b_copies r '' m1b_isometries
        (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap) := by
  rw [← m1b_isometries_conj e B, Set.image_image, Set.image_image]
  congr 1

theorem m1b_isometry_generation_conj_iff (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n ↔
    m1b_fixed (m1b_copies r '' m1b_isometries
      (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries
        (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)) 2) n := by
  simpa only [m1b_copies_isometries_conj] using
    m1b_generation_conj_iff (m1b_copiesEquiv e r)
      (m1b_copies r '' m1b_isometries B) n

theorem m1b_nondegenerate_transport (e : V ≃ₗ[ℂ] W)
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) :
    (B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap).Nondegenerate := by
  constructor
  · intro x hx
    apply e.symm.injective
    rw [map_zero]
    apply hB.1
    intro y
    simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hx (e y)
  · intro y hy
    apply e.symm.injective
    rw [map_zero]
    apply hB.2
    intro x
    simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hy (e x)

theorem m1b_orthogonal_rank_one_tensors [FiniteDimensional ℂ V]
    (hd : Module.finrank ℂ V = 1) (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n := by
  let e : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V ℂ (by simpa using hd)
  apply (m1b_isometry_generation_conj_iff e B r n).mpr
  exact m1b_orthogonal_line_tensors _ (m1b_nondegenerate_transport e B hB) r n

end HodgeLean.Foundations.Program

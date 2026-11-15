import HodgeLean.Foundations.SchurWeylLie
import HodgeLean.Foundations.Program.MilneTensorHelpers
import HodgeLean.Foundations.Abdulali.OrthogonalCharacter
import HodgeLean.Foundations.Program.MilneTensorProofs

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The top alternating tensor transforms by the determinant, including dimension zero.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17; the determinant character
on the top exterior power and its antisymmetrization in the tensor power. -/
theorem tensorPow_volume (u : Module.End ℂ V) :
    SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u
      (SchurWeyl.detTensorDual ℂ V) =
      LinearMap.det u • SchurWeyl.detTensorDual ℂ V := by
  classical
  let b := Module.finBasis ℂ V
  have hm : SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u
      (SchurWeyl.antisymTensor ℂ V _ b) =
      SchurWeyl.antisymTensor ℂ V _ (u ∘ b) := by
    simp only [SchurWeyl.antisymTensor_apply, map_sum, map_zsmul,
      SchurWeyl.tensorPow_tprod, Function.comp_apply]
  rw [SchurWeyl.detTensorDual_eq, hm]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  have hh := (ℓ.compAlternatingMap (SchurWeyl.antisymTensor ℂ V _)).eq_smul_basis_det b
  have h := congr($hh (u ∘ b))
  simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

/-- A volume tensor with an independent copy label in each slot.
Source: Weyl, The Classical Groups, Chapter II, §17, polarization of determinant
invariants on repeated copies of the standard representation. -/
def labeledVolume (r : ℕ) (a : Fin (Module.finrank ℂ V) → Fin r) :
    ⨂[ℂ]^(Module.finrank ℂ V) (Fin r → V) :=
  PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (a i))
    (SchurWeyl.detTensorDual ℂ V)

/-- Independent copy labels commute with the diagonal action.
Source: Weyl, The Classical Groups, Chapter II, §17, polarization of determinant
invariants on repeated copies. -/
theorem tensorPow_labeledVolume (r : ℕ)
    (a : Fin (Module.finrank ℂ V) → Fin r) (u : Module.End ℂ V) :
    SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) (m1b_copies r u)
      (labeledVolume r a) = LinearMap.det u • labeledVolume r a := by
  classical
  have hc : (SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) (m1b_copies r u)).comp
      (PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (a i))) =
      (PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (a i))).comp
        (SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u) := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      SchurWeyl.tensorPow_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i j
    change u ((Pi.single (a i) (v i) : Fin r → V) j) =
      (Pi.single (a i) (u (v i)) : Fin r → V) j
    simp only [Pi.single_apply]
    split_ifs <;> simp only [map_zero]
  change _ = LinearMap.det u •
    PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (a i)) _
  rw [← map_smul, ← tensorPow_volume u]
  exact LinearMap.congr_fun hc (SchurWeyl.detTensorDual ℂ V)

/-- Permuted products of full-orthogonal quadratic invariants and one labeled volume.
The number of quadratic factors may be zero, and the volume has degree `finrank ℂ V`.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, the determinant sector
of the orthogonal tensor theorem. -/
def orthogonalVolumeProducts (B : LinearMap.BilinForm ℂ V) (r n : ℕ) :
    Submodule ℂ (⨂[ℂ]^n (Fin r → V)) :=
  Submodule.span ℂ {t | ∃ (k : ℕ) (h : k + Module.finrank ℂ V = n)
      (σ : Equiv.Perm (Fin (k + Module.finrank ℂ V)))
      (a : ⨂[ℂ]^k (Fin r → V)) (c : Fin (Module.finrank ℂ V) → Fin r),
      a ∈ m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) k ∧
      t = h ▸ SchurWeyl.permRep ℂ (Fin r → V) _ σ
        (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
          (a ⊗ₜ[ℂ] labeledVolume r c))}

/-- Quadratic products and labeled volume products are fixed by the special orthogonal
operators, in every tensor degree and for every number of copies.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, invariance of the form
and determinant generators. This is the inclusion from generators into invariants. -/
theorem orthogonal_generators_le_special_fixed (B : LinearMap.BilinForm ℂ V) (r n : ℕ) :
    m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n ⊔
        orthogonalVolumeProducts B r n ≤
      m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | LinearMap.det u = 1}) n := by
  apply sup_le
  · intro t ht
    have hh : t ∈ m1b_fixed (m1b_copies r '' m1b_isometries B) n :=
      m1b_products_le_fixed (V := Fin r → V) (m1b_copies r '' m1b_isometries B) n ht
    simp only [m1b_fixed, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hh ⊢
    rintro _ ⟨u, hu, rfl⟩
    exact hh _ ⟨u, hu.1, rfl⟩
  · apply Submodule.span_le.mpr
    rintro t ⟨k, h, σ, a, c, ha, rfl⟩
    subst n
    dsimp only at *
    have hfa : a ∈ m1b_fixed (m1b_copies r '' m1b_isometries B) k :=
      m1b_products_le_fixed (V := Fin r → V) (m1b_copies r '' m1b_isometries B) k ha
    simp only [m1b_fixed, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfa ⊢
    rintro _ ⟨u, hu, rfl⟩
    have hc := LinearMap.congr_fun (SchurWeyl.permRep_mul_tensorPow σ (m1b_copies r u))
      (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
        (a ⊗ₜ[ℂ] labeledVolume r c))
    change _ = SchurWeyl.tensorPow _ (m1b_copies r u)
      (SchurWeyl.permRep ℂ (Fin r → V) _ σ
        (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
          (a ⊗ₜ[ℂ] labeledVolume r c))) at hc
    rw [← hc]
    change SchurWeyl.permRep ℂ (Fin r → V) _ σ
      (SchurWeyl.tensorPow _ (m1b_copies r u)
        (InvariantsExterior.tensorAppend k (Module.finrank ℂ V)
          (a ⊗ₜ[ℂ] labeledVolume r c))) = _
    rw [m1b_tensorPow_append, hfa _ ⟨u, hu.1, rfl⟩,
      tensorPow_labeledVolume, hu.2, one_smul]

/-- The scalar degree contains the tensor unit, with no restriction on the number of copies.
Source: Weyl, The Classical Groups, Chapter II, §17, the degree-zero invariant. -/
theorem special_orthogonal_tensor_generation_zero
    (B : LinearMap.BilinForm ℂ V) (r : ℕ) :
    m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | LinearMap.det u = 1}) 0 =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) 0 ⊔
        orthogonalVolumeProducts B r 0 := by
  rw [m1b_fixed_zero]
  simp only [m1b_products, top_sup_eq]

/-- The ordinary orthogonal FFT supplies the trivial-character sector. The additional
sector is the determinant eigenspace for the original space, rather than the determinant
of its repeated-copy representation.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17; Milne (1999), §3,
full orthogonal tensor generation. -/
theorem special_orthogonal_fixed_eq_quadratic_sup_character
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | LinearMap.det u = 1}) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n ⊔
      (⨅ g : orthogonalUnits B,
        LinearMap.ker (orthogonalTensorRepresentation B r n g -
          orthogonalDeterminant B g • LinearMap.id)) := by
  rw [← special_orthogonal_tensor_fixed_eq,
    orthogonal_tensor_character_decomposition B hB,
    orthogonal_tensor_fixed_eq, m1b_orthogonal_tensors_aux V B hB hs r n]

/-- Two labeled determinant blocks have trivial character and are therefore quadratic
products by the full orthogonal FFT. Thus additional volume blocks do not introduce
another sector.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, product of two determinant
characters; Milne (1999), §3, full orthogonal tensor generation. -/
theorem two_labeledVolumes_mem_quadratic_products
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r : ℕ)
    (a b : Fin (Module.finrank ℂ V) → Fin r) :
    InvariantsExterior.tensorAppend (Module.finrank ℂ V) (Module.finrank ℂ V)
        (labeledVolume r a ⊗ₜ[ℂ] labeledVolume r b) ∈
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2)
        (Module.finrank ℂ V + Module.finrank ℂ V) := by
  rw [← m1b_orthogonal_tensors_aux V B hB hs r]
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rintro _ ⟨u, ⟨⟨w, rfl⟩, hu⟩, rfl⟩
  have hd : LinearMap.det w.val * LinearMap.det w.val = 1 := by
    rcases orthogonalDeterminant_sign B hB ⟨w, hu⟩ with h | h
    · change LinearMap.det w.val = 1 at h
      rw [h]; norm_num
    · change LinearMap.det w.val = -1 at h
      rw [h]; norm_num
  rw [m1b_tensorPow_append, tensorPow_labeledVolume, tensorPow_labeledVolume]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    hd, one_smul, map_smul]

/-- Exact reduction of the tensor spanning equality to its additional character sector.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, the orthogonal character
split and determinant generators. No invariant-generation premise is introduced. -/
theorem special_orthogonal_generation_iff_character_spanning
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    (m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | LinearMap.det u = 1}) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n ⊔
        orthogonalVolumeProducts B r n) ↔
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (orthogonalTensorRepresentation B r n g -
        orthogonalDeterminant B g • LinearMap.id)) ≤
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n ⊔
        orthogonalVolumeProducts B r n := by
  have hgen := orthogonal_generators_le_special_fixed B r n
  rw [special_orthogonal_fixed_eq_quadratic_sup_character B hB hs r n] at hgen ⊢
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    exact le_antisymm (sup_le le_sup_left h) hgen

end HodgeLean.Foundations.Abdulali

import HodgeLean.Foundations.Program.MilneTensorRepresentationTransport
import HodgeLean.Foundations.Program.MilneTensorSmallIndexAlgebras
import HodgeLean.Foundations.Program.MilneTensorCopiesOne
import HodgeLean.Foundations.Program.MilneTensorPiNormOneReindex
import HodgeLean.Foundations.Program.MilneTensorPiInvolutionSplit
import HodgeLean.Foundations.Program.MilneTensorStableIdempotent
import HodgeLean.Foundations.Program.MilneTensorRepresentationAlgebraTransport
import HodgeLean.Foundations.Program.MilneTensorCopiesRepresentation
import HodgeLean.Foundations.Program.MilneTensorPiNormOneSplit
import HodgeLean.Foundations.Program.MilneTensorSingleRepresentation
import HodgeLean.Foundations.Program.MilneTensorExchangeRepresentation
import HodgeLean.Foundations.Program.MilneTensorNormOneAlgebraTransport
import HodgeLean.Foundations.Program.MilneTensorColoredProducts
import HodgeLean.Foundations.Program.MilneTensorExchangeGeneration
import HodgeLean.Foundations.Program.MilneTensorGLMultiplicity
import HodgeLean.Foundations.Program.MilneTensorCentralizerNormOne
import HodgeLean.Foundations.Program.MilneTensorNormOneTransport
import HodgeLean.Foundations.Program.MilneTensorGramNormOne
import HodgeLean.Foundations.Program.MilneFactors
import HodgeLean.Foundations.Program.MilneTensorStandardSymplectic
import HodgeLean.Foundations.Program.MilneTensorAlternatingStandardCoordinates
import HodgeLean.Foundations.Program.MilneTensorStandardOrthogonal
import HodgeLean.Foundations.Program.MilneTensorSymmetricStandardCoordinates
import HodgeLean.Foundations.Program.MilneTensorHelpers
import HodgeLean.Foundations.Program.MilneTensorNormal
import HodgeLean.Foundations.Program.MilneTensorIndependent
import HodgeLean.Foundations.Program.MilneTensorAlternating
import HodgeLean.Foundations.Program.MilneTensorMatrix

noncomputable section
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

theorem m1b_equivariant_matrix_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSemisimpleRing A] :
    ∃ (s : ℕ) (d m : Fin s → ℕ), (∀ i, 0 < d i ∧ 0 < m i) ∧
      ∃ (e : A ≃ₐ[ℂ] ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
        (E : V ≃ₗ[ℂ] ((i : Fin s) → Fin (m i) → Fin (d i) → ℂ)),
        ∀ (a : A) (v : V) (i : Fin s) (j : Fin (m i)),
          E ((a : Module.End ℂ V) v) i j = (e a i).mulVec (E v i j) := by
  classical
  obtain ⟨s, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  have hdpos (i : Fin s) : 0 < d i := Nat.pos_of_ne_zero (hd i).out
  let z : (i : Fin s) → Fin (d i) := fun i => ⟨0, hdpos i⟩
  let ρ : ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ]
      Module.End ℂ V := A.val.comp e.symm.toAlgHom
  have hρ : Function.Injective ρ := by
    intro x y h
    apply e.symm.injective
    exact Subtype.ext h
  refine ⟨s, d, fun i => Module.finrank ℂ (m1b_matrixMultiplicity d ρ z i),
    fun i => ⟨hdpos i, m1b_matrixMultiplicity_pos d ρ z hρ i⟩,
    e, m1b_matrixScalarCoordinates d ρ z, ?_⟩
  intro a v i j
  have h := m1b_matrixScalarCoordinates_action d ρ z (e a) v i j
  have he : ρ (e a) = (a : Module.End ℂ V) := by
    change ((e.symm (e a) : A) : Module.End ℂ V) = _
    rw [e.symm_apply_apply]
  rw [he] at h
  exact h

theorem m1b_symmetric_normal_aux (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = B) :
    ∃ P : (Matrix (Fin n) (Fin n) ℂ)ˣ, P.val.transpose * B * P.val = 1 := by
  classical
  have hsep (C : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C)
      (hCs : C.transpose = C) : C.toQuadraticForm'.associated.SeparatingLeft := by
    rw [m1b_associated_matrix n C hCs]
    exact (LinearMap.separatingLeft_toLinearMap₂'_iff_det_ne_zero).mpr
      (hC.map (Matrix.detMonoidHom)).ne_zero
  obtain ⟨e⟩ := QuadraticForm.equivalent_of_isAlgClosed
    (1 : Matrix (Fin n) (Fin n) ℂ).toQuadraticForm' B.toQuadraticForm'
    (hsep 1 isUnit_one (Matrix.transpose_one)) (hsep B hB hs)
  let P : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    { val := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
      inv := LinearMap.toMatrix' e.toLinearEquiv.symm.toLinearMap
      val_inv := by
        rw [← LinearMap.toMatrix'_mul]
        have he : e.toLinearEquiv.toLinearMap * e.toLinearEquiv.symm.toLinearMap = 1 := by
          apply LinearMap.ext
          intro x
          exact e.toLinearEquiv.apply_symm_apply x
        rw [he, LinearMap.toMatrix'_one]
      inv_val := by
        rw [← LinearMap.toMatrix'_mul]
        have he : e.toLinearEquiv.symm.toLinearMap * e.toLinearEquiv.toLinearMap = 1 := by
          apply LinearMap.ext
          intro x
          exact e.toLinearEquiv.symm_apply_apply x
        rw [he, LinearMap.toMatrix'_one] }
  refine ⟨P, ?_⟩
  have he : B.toQuadraticForm'.comp e.toLinearEquiv.toLinearMap =
      (1 : Matrix (Fin n) (Fin n) ℂ).toQuadraticForm' := by
    ext x
    exact e.map_app x
  have hm := congrArg QuadraticForm.toMatrix' he
  rw [QuadraticForm.toMatrix'_comp, m1b_matrix_quadratic_coordinates n B hs,
    m1b_matrix_quadratic_coordinates n 1 Matrix.transpose_one] at hm
  exact hm

theorem m1b_alternating_normal_aux (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) (hs : B.transpose = -B) :
    ∃ (k : ℕ) (e : Fin n ≃ (Fin k ⊕ Fin k))
      (P : (Matrix (Fin n) (Fin n) ℂ)ˣ),
      n = 2 * k ∧ P.val.transpose * B * P.val =
        Matrix.reindex e.symm e.symm (m1b_J k) := by
  classical
  obtain ⟨k, b, hk, hb⟩ := m1b_alternating_basis n B hB hs
  let e : Fin n ≃ (Fin k ⊕ Fin k) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sum]
    omega)
  let b' := b.reindex e.symm
  let E := b'.equivFun.symm
  have hE (i : Fin n) : E (Pi.single i 1) = b (e i) := by
    simp [E, b', Module.Basis.equivFun_symm_apply]
  refine ⟨k, e, m1b_matrix_unit n E, hk, ?_⟩
  change (LinearMap.toMatrix' E.toLinearMap).transpose * B *
    LinearMap.toMatrix' E.toLinearMap = _
  calc _ = LinearMap.toMatrix₂' ℂ
        (B.toBilin'.compl₁₂ E.toLinearMap E.toLinearMap) := by
          rw [LinearMap.toMatrix₂'_compl₁₂]
          rw [show LinearMap.toMatrix₂' ℂ B.toBilin' = B from
            (LinearMap.toMatrix₂' ℂ).apply_symm_apply B]
       _ = _ := by
         ext i j
         rw [LinearMap.toMatrix₂'_apply, LinearMap.compl₁₂_apply]
         change B.toBilin' (E (Pi.single i 1)) (E (Pi.single j 1)) =
           m1b_J k (e i) (e j)
         rw [hE, hE]
         exact hb _ _

theorem m1b_exchange_normal_aux (n : ℕ)
    (τ : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℂ]
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hswap : τ (1, 0) = (0, 1)) :
    ∃ e : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ),
      ∀ a, e (τ a) = m1_exchange n (e a) := by
  classical
  let M := Matrix (Fin n) (Fin n) ℂ
  have hswap' : τ (0, 1) = (1, 0) := by rw [← hswap, hτ]
  have hleft (a : M) : (τ (a, 0)).1 = 0 := by
    have h := congrArg Prod.fst (hmul (a, 0) (1, 0))
    simpa only [Prod.mk_mul_mk, mul_one, mul_zero, hswap, Prod.fst_mul,
      Prod.fst_zero, Prod.fst_one, zero_mul] using h
  have hright (b : M) : (τ (0, b)).2 = 0 := by
    have h := congrArg Prod.snd (hmul (0, b) (0, 1))
    simpa only [Prod.mk_mul_mk, mul_one, mul_zero, hswap', Prod.snd_mul,
      zero_mul] using h
  have hparts (a b : M) : τ (a, b) = ((τ (0, b)).1, (τ (a, 0)).2) := by
    have h : (a, b) = (a, 0) + (0, b) := by simp
    rw [h, map_add]
    ext <;> simp [hleft, hright]
  have hreturn₁ (a : M) : (τ (0, (τ (a, 0)).2)).1 = a := by
    have h := congrArg Prod.fst (hτ (a, 0))
    have hh : τ (a, 0) = (0, (τ (a, 0)).2) := Prod.ext (hleft a) rfl
    rwa [hh] at h
  have hreturn₂ (b : M) : (τ ((τ (0, b)).1, 0)).2 = b := by
    have h := congrArg Prod.snd (hτ (0, b))
    have hh : τ (0, b) = ((τ (0, b)).1, 0) := Prod.ext rfl (hright b)
    rwa [hh] at h
  let f : M →ₗ[ℂ] M :=
    Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ |>.toLinearMap |>.comp
      ((LinearMap.fst ℂ M M).comp (τ.toLinearMap.comp (LinearMap.inr ℂ M M)))
  let g : M →ₗ[ℂ] M := (LinearMap.snd ℂ M M).comp
    (τ.toLinearMap.comp ((LinearMap.inl ℂ M M).comp
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap))
  have hgf (b : M) : g (f b) = b := by
    change (τ (((τ (0, b)).1.transpose).transpose, 0)).2 = b
    rw [Matrix.transpose_transpose, hreturn₂]
  have hfg (a : M) : f (g a) = a := by
    change (τ (0, (τ (a.transpose, 0)).2)).1.transpose = a
    rw [hreturn₁, Matrix.transpose_transpose]
  let E : (M × M) ≃ₗ[ℂ] (M × M) :=
    { toLinearMap := (LinearMap.id : M →ₗ[ℂ] M).prodMap f
      invFun := fun p => (p.1, g p.2)
      left_inv := fun p => Prod.ext rfl (hgf p.2)
      right_inv := fun p => Prod.ext rfl (hfg p.2) }
  let e : (M × M) ≃ₐ[ℂ] (M × M) :=
    AlgEquiv.ofLinearEquiv E (by
      change (1, (τ (0, 1)).1.transpose) = (1, 1)
      rw [hswap', Matrix.transpose_one]) (by
      intro a b
      apply Prod.ext
      · rfl
      · change (τ (0, a.2 * b.2)).1.transpose =
          (τ (0, a.2)).1.transpose * (τ (0, b.2)).1.transpose
        have h := congrArg Prod.fst (hmul (0, a.2) (0, b.2))
        simp only [Prod.mk_mul_mk, zero_mul, Prod.fst_mul] at h
        rw [h, Matrix.transpose_mul])
  refine ⟨e, ?_⟩
  intro a
  change ((τ a).1, (τ (0, (τ a).2)).1.transpose) =
    (((τ (0, a.2)).1.transpose).transpose, a.1.transpose)
  rw [Matrix.transpose_transpose]
  have hp := hparts a.1 a.2
  change τ a = _ at hp
  rw [hp, hreturn₁]

theorem m1b_orthogonal_tensors_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hs : ∀ x y, B x y = B y x) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n := by
  classical
  obtain ⟨e, he⟩ := m1b_symmetric_standard_coordinates B hB hs
  apply (m1b_isometry_generation_conj_iff e B r n).mpr
  rw [he]
  exact m1b_standard_orthogonal_generation (Module.finrank ℂ V) r n

theorem m1b_symplectic_tensors_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (ha : ∀ x, B x x = 0) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n := by
  classical
  obtain ⟨k, e, he⟩ := m1b_alternating_standard_coordinates B hB ha
  apply (m1b_isometry_generation_conj_iff e B r n).mpr
  rw [he]
  exact m1b_standard_symplectic_generation k r n

theorem m1b_gram_norm_one_tensors (d : ℕ) (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : IsUnit B) (hsign : B.transpose = B ∨ B.transpose = -B) (r n : ℕ) :
    m1b_fixed (m1b_copies r ''
      (Matrix.toLin' '' {X | m1_gramAdjoint d B X * X = 1})) n =
      m1b_products (m1b_fixed (m1b_copies r ''
        (Matrix.toLin' '' {X | m1_gramAdjoint d B X * X = 1})) 2) n := by
  rw [m1b_gram_norm_one_image d B hB]
  have hnd : B.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
      (hB.map Matrix.detMonoidHom).ne_zero
  rcases hsign with hs | ha
  · exact m1b_orthogonal_tensors_aux _ B.toBilin' hnd
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr hs).eq r n
  · exact m1b_symplectic_tensors_aux _ B.toBilin' hnd
      (m1b_matrix_bilin_alternating B ha) r n

theorem m1b_simple_matrix_tensors (d : ℕ) (hd : 0 < d)
    (τ : Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hτ : Function.Involutive τ) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' (Matrix.toLin' '' {X | τ X * X = 1})) n =
      m1b_products (m1b_fixed (m1b_copies r ''
        (Matrix.toLin' '' {X | τ X * X = 1})) 2) n := by
  obtain ⟨B, hB, hsign, hτB⟩ := m1_simple_involution d hd τ hτ hmul
  simp_rw [hτB]
  exact m1b_gram_norm_one_tensors d B hB hsign r n

theorem m1b_simple_factor_tensors (V : Type*) [AddCommGroup V] [Module ℂ V]
    (A : Subalgebra ℂ (Module.End ℂ V)) (d m : ℕ) (hd : 0 < d)
    (e : A ≃ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (E : V ≃ₗ[ℂ] (Fin m → Fin d → ℂ))
    (τ : A ≃ₗ[ℂ] A)
    (σ : Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hσ : Function.Involutive σ) (hmul : ∀ X Y, σ (X * Y) = σ Y * σ X)
    (hτσ : ∀ a, σ (e a) = e (τ a))
    (hE : ∀ (a : A) (v : V) (j : Fin m),
      E ((a : Module.End ℂ V) v) j = (e a).mulVec (E v j)) (r n : ℕ) :
    m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) n =
      m1b_products (m1b_fixed (m1b_copies r ''
        {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) 2) n := by
  let ρ₀ : Module.End ℂ (Fin d → ℂ) →ₐ[ℂ]
      Module.End ℂ (Fin m → Fin d → ℂ) :=
    { toFun := m1b_copies m
      map_one' := by ext v j i; rfl
      map_mul' := by intros; ext v j i; rfl
      map_zero' := by ext v j i; rfl
      map_add' := by intros; ext v j i; rfl
      commutes' := by intro z; ext v j i; rfl }
  let ρ := ρ₀.comp (Matrix.toLinAlgEquiv' :
    Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom
  have hE' (a : A) (v : V) : E ((a : Module.End ℂ V) v) = ρ (e a) (E v) := by
    funext j
    exact hE a v j
  have hset := m1b_norm_one_image_conj A e E ρ τ σ hτσ hE'
  have hρ : {u | ∃ b, ρ b = u ∧ σ b * b = 1} =
      m1b_copies m '' (Matrix.toLin' '' {X | σ X * X = 1}) := by
    ext u
    constructor
    · rintro ⟨b, rfl, hb⟩
      exact ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, rfl, hb⟩
  rw [hρ] at hset
  apply (m1b_generation_conj_iff (m1b_copiesEquiv E r) _ n).mpr
  rw [m1b_copies_conj_image, hset]
  exact m1b_copies_generation _ r n (m1b_simple_matrix_tensors d hd σ hσ hmul m n)

theorem m1b_independent_factors_aux (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (hS : 1 ∈ S) (hT : 1 ∈ T) :
    (⨅ u ∈ S, ⨅ v ∈ T, LinearMap.ker (TensorProduct.map u v - LinearMap.id)) =
      Submodule.span ℂ {z : V ⊗[ℂ] W | ∃ x y,
        (∀ u ∈ S, u x = x) ∧ (∀ v ∈ T, v y = y) ∧ z = x ⊗ₜ[ℂ] y} := by
  classical
  let P : Submodule ℂ V := ⨅ u ∈ S, LinearMap.ker (u - LinearMap.id)
  apply le_antisymm
  · intro t ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at ht
    obtain ⟨z, hz⟩ := m1b_fixed_left_lift S t (fun u hu => ht u hu 1 hT)
    have hinj : Function.Injective (TensorProduct.map P.subtype (LinearMap.id : W →ₗ[ℂ] W)) :=
      TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id
    have hzv (v) (hv : v ∈ T) : TensorProduct.map LinearMap.id v z = z := by
      apply hinj
      have hm : (TensorProduct.map P.subtype (LinearMap.id : W →ₗ[ℂ] W)).comp
          (TensorProduct.map LinearMap.id v) =
          (TensorProduct.map (LinearMap.id : V →ₗ[ℂ] V) v).comp
            (TensorProduct.map P.subtype LinearMap.id) := by
        ext x y
        rfl
      rw [← LinearMap.comp_apply, hm, LinearMap.comp_apply, hz]
      exact ht 1 hS v hv
    let b := Module.Free.chooseBasis ℂ P
    let c := TensorProduct.equivFinsuppOfBasisLeft b z
    have hc (i) (v) (hv : v ∈ T) : v (c i) = c i := by
      change v (TensorProduct.equivFinsuppOfBasisLeft b z i) = _
      rw [← m1b_left_coeff_map, hzv v hv]
    have hzsum : (∑ i ∈ c.support, b i ⊗ₜ[ℂ] c i) = z :=
      by simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] using
        (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z
    rw [← hz, ← hzsum]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    refine ⟨(b i : V), c i, ?_, hc i, rfl⟩
    have hb := (b i).property
    simpa only [P, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] using hb
  · apply Submodule.span_le.mpr
    rintro t ⟨x, y, hx, hy, rfl⟩
    change x ⊗ₜ[ℂ] y ∈ (⨅ u ∈ S, ⨅ v ∈ T,
      LinearMap.ker (TensorProduct.map u v - LinearMap.id))
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro u hu v hv
    rw [TensorProduct.map_tmul, hx u hu, hy v hv]

theorem m1b_colored_fixed_aux (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (n : ℕ) (t : ⨂[ℂ]^n (V × W)) :
    (∀ u ∈ S, ∀ v ∈ T, SchurWeyl.tensorPow (Fin n) (u.prodMap v) t = t) ↔
      ∀ (s : Finset (Fin n)) u, u ∈ S → ∀ v, v ∈ T →
        TensorProduct.map (SchurWeyl.tensorPow {i // i ∈ s} u)
          (SchurWeyl.tensorPow {i // i ∉ s} v)
          (InvariantsExterior.coloredWordOut s t) =
            InvariantsExterior.coloredWordOut s t := by
  classical
  constructor
  · intro h s u hu v hv
    rw [← m1b_coloredWordOut_tensorPow, h u hu v hv]
  · intro h u hu v hv
    have hc : ∀ s : Finset (Fin n),
        InvariantsExterior.coloredWordOut s
          (SchurWeyl.tensorPow (Fin n) (u.prodMap v) t) =
          InvariantsExterior.coloredWordOut s t := by
      intro s
      rw [m1b_coloredWordOut_tensorPow, h s u hu v hv]
    calc SchurWeyl.tensorPow (Fin n) (u.prodMap v) t =
        ∑ s : Finset (Fin n), InvariantsExterior.coloredWordIn s
          (InvariantsExterior.coloredWordOut s
            (SchurWeyl.tensorPow (Fin n) (u.prodMap v) t)) :=
              (InvariantsExterior.sum_coloredWordIn_out _).symm
      _ = ∑ s : Finset (Fin n), InvariantsExterior.coloredWordIn s
          (InvariantsExterior.coloredWordOut s t) := by simp_rw [hc]
      _ = t := InvariantsExterior.sum_coloredWordIn_out t

theorem m1b_prod_generation (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Set (Module.End ℂ V)) (T : Set (Module.End ℂ W))
    (hS1 : 1 ∈ S) (hT1 : 1 ∈ T)
    (hS : ∀ k, m1b_fixed S k = m1b_products (m1b_fixed S 2) k)
    (hT : ∀ k, m1b_fixed T k = m1b_products (m1b_fixed T 2) k) (n : ℕ) :
    m1b_fixed (Set.image2 (fun u v => u.prodMap v) S T) n =
      m1b_products (m1b_fixed (Set.image2 (fun u v => u.prodMap v) S T) 2) n := by
  classical
  apply le_antisymm
  · intro t ht
    have htf : ∀ u ∈ S, ∀ v ∈ T,
        SchurWeyl.tensorPow (Fin n) (u.prodMap v) t = t := by
      have hf : ∀ u ∈ Set.image2 (fun u v => u.prodMap v) S T,
          SchurWeyl.tensorPow (Fin n) u t = t := by
        simpa only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
          LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using ht
      exact fun u hu v hv => hf _ ⟨u, hu, v, hv, rfl⟩
    rw [← InvariantsExterior.sum_coloredWordIn_out t]
    apply Submodule.sum_mem
    intro s _
    let FirstSlots := {i : Fin n // i ∈ s}
    let SecondSlots := {i : Fin n // i ∉ s}
    let S' := SchurWeyl.tensorPow FirstSlots '' S
    let T' := SchurWeyl.tensorPow SecondSlots '' T
    have hS' : 1 ∈ S' := ⟨1, hS1, SchurWeyl.tensorPow_one⟩
    have hT' : 1 ∈ T' := ⟨1, hT1, SchurWeyl.tensorPow_one⟩
    have hw : InvariantsExterior.coloredWordOut s t ∈
        (⨅ u ∈ S', ⨅ v ∈ T', LinearMap.ker (TensorProduct.map u v - LinearMap.id)) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← m1b_coloredWordOut_tensorPow, htf u hu v hv]
    rw [m1b_independent_factors_aux _ _ S' T' hS' hT'] at hw
    generalize hz : InvariantsExterior.coloredWordOut s t = z at hw ⊢
    clear hz
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, y, hx, hy, rfl⟩ := hw
      exact m1b_coloredWordIn_products S T hS hT n s x y
        (fun u hu => hx _ ⟨u, hu, rfl⟩) (fun v hv => hy _ ⟨v, hv, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx => rw [map_smul]; exact Submodule.smul_mem _ c ihx
  · exact m1b_products_le_fixed _ n

theorem m1b_simple_representation_tensors (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (hd : 0 < d)
    (ρ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ V)
    (τ : Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hτ : Function.Involutive τ) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' (ρ '' {X | τ X * X = 1})) n =
      m1b_products (m1b_fixed (m1b_copies r '' (ρ '' {X | τ X * X = 1})) 2) n := by
  obtain ⟨a, E, hE⟩ := m1b_matrix_single_coordinates d hd ρ
  have hconj (X) : E.conj (ρ X) = m1b_copies a X.toLin' := by
    apply LinearMap.ext
    intro v
    funext j
    change E (ρ X (E.symm v)) j = X.mulVec (v j)
    simpa only [E.apply_symm_apply] using hE X (E.symm v) j
  have hset : E.conj '' (ρ '' {X | τ X * X = 1}) =
      m1b_copies a '' (Matrix.toLin' '' {X | τ X * X = 1}) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext X
    exact hconj X
  apply (m1b_generation_conj_iff (m1b_copiesEquiv E r) _ n).mpr
  rw [m1b_copies_conj_image, hset]
  exact m1b_copies_generation _ r n (m1b_simple_matrix_tensors d hd τ hτ hmul a n)

theorem m1b_exchanged_representation_tensors (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (hd : 0 < d)
    (ρ : (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) →ₐ[ℂ] Module.End ℂ V)
    (τ : (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) ≃ₗ[ℂ]
      (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X)
    (hswap : τ (1, 0) = (0, 1)) (r n : ℕ) :
    m1b_fixed (m1b_copies r '' (ρ '' {X | τ X * X = 1})) n =
      m1b_products (m1b_fixed (m1b_copies r '' (ρ '' {X | τ X * X = 1})) 2) n := by
  obtain ⟨e, he⟩ := m1b_exchange_normal_aux d τ hτ hmul hswap
  have hnorm := m1b_norm_one_algEquiv_image e τ (m1_exchange d) (fun X => (he X).symm)
  have himage : ρ '' {X | τ X * X = 1} =
      (ρ.comp e.symm.toAlgHom) '' {X | m1_exchange d X * X = 1} := by
    rw [← hnorm, Set.image_image]
    congr 1
    funext X
    change ρ X = ρ (e.symm (e X))
    rw [e.symm_apply_apply]
  rw [himage]
  exact m1b_exchange_representation_tensors d hd (ρ.comp e.symm.toAlgHom) r n

theorem m1b_pi_norm_one_split_generation (I : Type*) (R M : I → Type*)
    [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (ρ : (i : I) → R i →ₐ[ℂ] Module.End ℂ (M i)) (p : I → Prop) [DecidablePred p]
    (τ : ((i : I) → R i) ≃ₗ[ℂ] ((i : I) → R i))
    (α : ((i : {i // p i}) → R i.val) ≃ₗ[ℂ] ((i : {i // p i}) → R i.val))
    (β : ((i : {i // ¬p i}) → R i.val) ≃ₗ[ℂ] ((i : {i // ¬p i}) → R i.val))
    (hαmul : ∀ a b, α (a * b) = α b * α a)
    (hβmul : ∀ a b, β (a * b) = β b * β a)
    (hparts : ∀ X, m1b_piSplitAlgEquiv R p (τ X) =
      (α (m1b_piSplitAlgEquiv R p X).1, β (m1b_piSplitAlgEquiv R p X).2))
    (hαgen : ∀ k,
      m1b_fixed (m1b_piRepresentation (fun i : {i // p i} => ρ i.val) '' {a | α a * a = 1}) k =
        m1b_products (m1b_fixed
          (m1b_piRepresentation (fun i : {i // p i} => ρ i.val) '' {a | α a * a = 1}) 2) k)
    (hβgen : ∀ k,
      m1b_fixed (m1b_piRepresentation (fun i : {i // ¬p i} => ρ i.val) '' {a | β a * a = 1}) k =
        m1b_products (m1b_fixed
          (m1b_piRepresentation (fun i : {i // ¬p i} => ρ i.val) '' {a | β a * a = 1}) 2) k)
    (n : ℕ) :
    m1b_fixed (m1b_piRepresentation ρ '' {X | τ X * X = 1}) n =
      m1b_products (m1b_fixed (m1b_piRepresentation ρ '' {X | τ X * X = 1}) 2) n := by
  apply (m1b_generation_conj_iff (m1b_piSplitModuleEquiv M p) _ n).mpr
  rw [m1b_pi_norm_one_split_image ρ p τ α β hparts]
  apply m1b_prod_generation _ _ _ _ _ _ hαgen hβgen n
  · refine ⟨1, ?_, map_one _⟩
    change α 1 * 1 = 1
    rw [m1b_involution_one α hαmul, one_mul]
  · refine ⟨1, ?_, map_one _⟩
    change β 1 * 1 = 1
    rw [m1b_involution_one β hβmul, one_mul]

theorem m1b_pi_matrix_norm_one_tensors (s : ℕ) :
    ∀ (d : Fin s → ℕ) (hd : ∀ i, 0 < d i) (M : Fin s → Type*)
      [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, FiniteDimensional ℂ (M i)]
      (ρ : (i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ →ₐ[ℂ] Module.End ℂ (M i))
      (τ : ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
        ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
      (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (n : ℕ),
      m1b_fixed (m1b_piRepresentation ρ '' {X | τ X * X = 1}) n =
        m1b_products (m1b_fixed (m1b_piRepresentation ρ '' {X | τ X * X = 1}) 2) n := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro d hd M instAdd instMod instFin ρ τ hτ hmul n
    classical
    by_cases hs : s = 0
    · subst s
      exact m1b_generation_subsingleton _ n
    have hspos : 0 < s := Nat.pos_of_ne_zero hs
    let i₀ : Fin s := ⟨0, hspos⟩
    let R : Fin s → Type := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ
    obtain ⟨σ, hσ, hσd, hσid⟩ := m1_involution_blocks s d hd τ hτ hmul
    have hblock : ∀ i, τ (Pi.single i 1) = Pi.single (σ i) 1 := hσid
    let p : Fin s → Prop := fun i => i = i₀ ∨ i = σ i₀
    have hp : ∀ j, p (σ j) ↔ p j := by
      intro j
      constructor
      · rintro (h | h)
        · right
          calc j = σ (σ j) := (hσ j).symm
               _ = σ i₀ := congrArg σ h
        · left
          exact σ.injective h
      · rintro (rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl (hσ i₀)
    by_cases hout : ∃ j, ¬p j
    · obtain ⟨j, hj⟩ := hout
      have hid := m1b_involution_piId R τ hmul σ hblock p hp
      obtain ⟨α, β, hα, hβ, hαmul, hβmul, hparts⟩ :=
        m1b_pi_involution_split R p τ hτ hmul hid
      refine m1b_pi_norm_one_split_generation (Fin s) R M ρ p τ α β hαmul hβmul hparts ?_ ?_ n
      · intro k
        have hlt : Fintype.card {i : Fin s // p i} < s := by
          simpa only [Fintype.card_fin] using Fintype.card_subtype_lt (p := p) (x := j) hj
        let e : Fin (Fintype.card {i : Fin s // p i}) ≃ {i : Fin s // p i} :=
          (Fintype.equivFin _).symm
        let eA := (AlgEquiv.piCongrLeft ℂ (fun i : {i // p i} => R i.val) e).symm
        let tauCoords := m1b_transportInvolution eA α
        have hTauCoords := m1b_transportInvolution_properties eA α hα hαmul
        have he (X) : tauCoords (eA X) = eA (α X) := by
          change eA (α (eA.symm (eA X))) = eA (α X)
          rw [eA.symm_apply_apply]
        apply m1b_pi_norm_one_reindex_generation (fun i : {i // p i} => ρ i.val) e α tauCoords he k
        exact ih _ hlt (fun i => d (e i).val) (fun i => hd (e i).val)
          (fun i => M (e i).val) (fun i => ρ (e i).val) tauCoords hTauCoords.1 hTauCoords.2 k
      · intro k
        have hi₀ : ¬(¬p i₀) := not_not.mpr (Or.inl rfl)
        have hlt : Fintype.card {i : Fin s // ¬p i} < s := by
          simpa only [Fintype.card_fin] using Fintype.card_subtype_lt (p := fun i : Fin s => ¬p i) (x := i₀) hi₀
        let e : Fin (Fintype.card {i : Fin s // ¬p i}) ≃ {i : Fin s // ¬p i} :=
          (Fintype.equivFin _).symm
        let eA := (AlgEquiv.piCongrLeft ℂ (fun i : {i // ¬p i} => R i.val) e).symm
        let tauCoords := m1b_transportInvolution eA β
        have hTauCoords := m1b_transportInvolution_properties eA β hβ hβmul
        have he (X) : tauCoords (eA X) = eA (β X) := by
          change eA (β (eA.symm (eA X))) = eA (β X)
          rw [eA.symm_apply_apply]
        apply m1b_pi_norm_one_reindex_generation (fun i : {i // ¬p i} => ρ i.val) e β tauCoords he k
        exact ih _ hlt (fun i => d (e i).val) (fun i => hd (e i).val)
          (fun i => M (e i).val) (fun i => ρ (e i).val) tauCoords hTauCoords.1 hTauCoords.2 k
    · have hcover (j : Fin s) : p j := by
        by_contra hj
        exact hout ⟨j, hj⟩
      by_cases hfix : σ i₀ = i₀
      · have huniq (j : Fin s) : j = i₀ := by
          rcases hcover j with h | h
          · exact h
          · exact h.trans hfix
        letI : Unique (Fin s) := { default := i₀, uniq := huniq }
        let eA := m1b_matrixUniqueAlgEquiv (Fin s) d
        let tauCoords := m1b_transportInvolution eA τ
        have hTauCoords := m1b_transportInvolution_properties eA τ hτ hmul
        have he (X) : tauCoords (eA X) = eA (τ X) := by
          change eA (τ (eA.symm (eA X))) = eA (τ X)
          rw [eA.symm_apply_apply]
        rw [m1b_norm_one_representation_algEquiv_image (m1b_piRepresentation ρ) eA τ tauCoords he]
        apply m1b_generation_of_copies_one
        exact m1b_simple_representation_tensors _ (d default) (hd default)
          ((m1b_piRepresentation ρ).comp eA.symm.toAlgHom) tauCoords hTauCoords.1 hTauCoords.2 1 n
      · let f : Fin 2 → Fin s := fun z => if z = 0 then i₀ else σ i₀
        have hf : Function.Bijective f := by
          constructor
          · intro a b hab
            fin_cases a <;> fin_cases b
            · rfl
            · change i₀ = σ i₀ at hab
              exact False.elim (hfix hab.symm)
            · change σ i₀ = i₀ at hab
              exact False.elim (hfix hab)
            · rfl
          · intro j
            rcases hcover j with h | h
            · exact ⟨0, h.symm⟩
            · exact ⟨1, h.symm⟩
        let eI := Equiv.ofBijective f hf
        have hdall (j : Fin s) : d j = d i₀ := by
          rcases hcover j with h | h
          · exact congrArg d h
          · exact (congrArg d h).trans (hσd i₀)
        let eA := m1b_matrixPairIndexAlgEquiv d (d i₀) hdall eI
        have hids := m1b_matrixPairIndex_ids d (d i₀) hdall eI
        let tauCoords := m1b_transportInvolution eA τ
        have hTauCoords := m1b_transportInvolution_properties eA τ hτ hmul
        have he (X) : tauCoords (eA X) = eA (τ X) := by
          change eA (τ (eA.symm (eA X))) = eA (τ X)
          rw [eA.symm_apply_apply]
        have hswap : tauCoords (1, 0) = (0, 1) := by
          change eA (τ (eA.symm (1, 0))) = (0, 1)
          rw [← hids.1, eA.symm_apply_apply, hblock]
          exact hids.2
        rw [m1b_norm_one_representation_algEquiv_image (m1b_piRepresentation ρ) eA τ tauCoords he]
        apply m1b_generation_of_copies_one
        exact m1b_exchanged_representation_tensors _ (d i₀) (hd i₀)
          ((m1b_piRepresentation ρ).comp eA.symm.toAlgHom) tauCoords hTauCoords.1 hTauCoords.2 hswap 1 n

theorem m1b_norm_one_tensors_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSemisimpleRing A]
    (τ : A ≃ₗ[ℂ] A) (hτ : Function.Involutive τ)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (r n : ℕ) :
    m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) n =
    m1b_products (m1b_fixed (m1b_copies r ''
      {u | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1}) 2) n := by
  classical
  obtain ⟨s, d, m, hdm, e, E, hE⟩ := m1b_equivariant_matrix_aux V A
  let ρ := m1b_piRepresentation (fun i : Fin s => m1b_matrixCopiesRepresentation (d i) (m i))
  let tauCoords := m1b_transportInvolution e τ
  have hTauCoords := m1b_transportInvolution_properties e τ hτ hmul
  have he (a : A) : tauCoords (e a) = e (τ a) := by
    change e (τ (e.symm (e a))) = e (τ a)
    rw [e.symm_apply_apply]
  have hmodule (a : A) (v : V) : E ((a : Module.End ℂ V) v) = ρ (e a) (E v) := by
    funext i j
    change E ((a : Module.End ℂ V) v) i j = (e a i).mulVec (E v i j)
    exact hE a v i j
  have himage := m1b_representation_norm_one_conj_image A.val ρ e E τ tauCoords he hmodule
  have hset : {u : Module.End ℂ V | ∃ a : A, (a : Module.End ℂ V) = u ∧ τ a * a = 1} =
      A.val '' {a | τ a * a = 1} := by
    ext u
    constructor
    · rintro ⟨a, rfl, ha⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, rfl, ha⟩
  rw [hset]
  apply (m1b_generation_conj_iff (m1b_copiesEquiv E r) _ n).mpr
  rw [m1b_copies_conj_image, himage]
  apply m1b_copies_generation
  exact m1b_pi_matrix_norm_one_tensors s d (fun i => (hdm i).1)
    (fun i => Fin (m i) → Fin (d i) → ℂ)
    (fun i => m1b_matrixCopiesRepresentation (d i) (m i)) tauCoords hTauCoords.1 hTauCoords.2 n

theorem m1b_centralizer_tensors_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r n : ℕ) :
    m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) n =
      m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) n := by
  letI := (torusCohomology_cupProductOf J).finite
  letI := m1_centralizer_semisimple J
  obtain ⟨τ, hτ, hmul, hadj⟩ := m1_centralizer_involution J pol hη hpos
  have hdiag : (fun u => g32p_diag J u r) = m1b_copies r := by
    funext u
    ext v i
    rfl
  rw [hdiag, m1b_centralizer_norm_one_set J pol hη τ hadj]
  exact m1b_norm_one_tensors_aux _ (m0_endCentralizer J) τ hτ hmul r n

end HodgeLean.Foundations.Program

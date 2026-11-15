import HodgeLean.Adapters.IntersectionProductMovingRobertsGeneric
import HodgeLean.Adapters.IntersectionProductMovingHomog

/-! # Linear projections and cones with a linear vertex

A linear projection `ℙᴺ ⇢ ℙⁿ` is given by `n + 1` linear forms `ℓ_i = Σ_k ℓ_{ik} x_k`, that is by
the substitution `a3r_lin ℓ : ℂ[y_0, …, y_n] → ℂ[x_0, …, x_N]`. The cone `C_L(V)` over a
subvariety `V = V(P)` with vertex the centre `L = V(ℓ)` is `ℓ⁻¹(ℓ(V))`, with ideal the extension
of the contraction `P ∩ ℂ[ℓ]` (`a3r_cone`). When the forms are part of a coordinate system, that
is rows of an invertible matrix, the cone over a prime is prime of dimension
`dim ℂ[ℓ]/(P ∩ ℂ[ℓ]) + N - n` (`a3r_cone_isPrime`), and the cone over a homogeneous ideal is
homogeneous. For generic `ℓ` the forms extend to a coordinate system by standard basis
vectors (`a3r_generic_ext_det`).

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96, §1
(the cone `C_L(V)`); Harris, *Algebraic Geometry: A First Course*, Lecture 3 (cones and linear
projections). HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial

namespace HodgeLean.Adapters

/-! ## Linear substitutions -/

section Linear

variable {ρ σ τ : Type} [Fintype ρ] [Fintype σ] [Fintype τ]

/-- The linear substitution `y_i ↦ Σ_k ℓ_{ik} x_k`. -/
def a3r_lin (ℓ : Matrix ρ σ ℂ) : MvPolynomial ρ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun i => ∑ k, C (ℓ i k) * X k

omit [Fintype ρ] in
theorem a3r_lin_X (ℓ : Matrix ρ σ ℂ) (i : ρ) : a3r_lin ℓ (X i) = ∑ k, C (ℓ i k) * X k :=
  aeval_X _ _

omit [Fintype ρ] in
theorem a3r_lin_C (ℓ : Matrix ρ σ ℂ) (c : ℂ) : a3r_lin ℓ (C c) = C c := by
  simp [a3r_lin]

omit [Fintype ρ] in
theorem a3r_lin_mul (g : Matrix ρ τ ℂ) (h : Matrix τ σ ℂ) :
    a3r_lin (g * h) = (a3r_lin h).comp (a3r_lin g) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, a3r_lin_X, a3r_lin_X, map_sum]
  have h1 : ∀ k : τ, a3r_lin h (C (g i k) * X k) = ∑ t, C (g i k) * C (h k t) * X t := by
    intro k
    rw [map_mul, a3r_lin_C, a3r_lin_X, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => (mul_assoc _ _ _).symm
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [C_mul]

theorem a3r_lin_one [DecidableEq σ] : a3r_lin (1 : Matrix σ σ ℂ) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [a3r_lin_X, AlgHom.id_apply]
  simp [Matrix.one_apply]

/-- An invertible substitution is an automorphism. -/
def a3r_linEquiv [DecidableEq σ] (g : Matrix σ σ ℂ) (hg : IsUnit g.det) :
    MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ :=
  AlgEquiv.ofAlgHom (a3r_lin g) (a3r_lin g⁻¹)
    (by rw [← a3r_lin_mul, Matrix.nonsing_inv_mul g hg, a3r_lin_one])
    (by rw [← a3r_lin_mul, Matrix.mul_nonsing_inv g hg, a3r_lin_one])

theorem a3r_linEquiv_apply [DecidableEq σ] (g : Matrix σ σ ℂ) (hg : IsUnit g.det)
    (F : MvPolynomial σ ℂ) : a3r_linEquiv g hg F = a3r_lin g F := rfl

omit [Fintype ρ] in
theorem a3r_lin_submatrix (g : Matrix σ σ ℂ) (e : ρ → σ) :
    a3r_lin (g.submatrix e id) = (a3r_lin g).comp (rename e) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, rename_X, a3r_lin_X, a3r_lin_X]
  rfl

omit [Fintype ρ] in
theorem a3r_lin_scale (ℓ : Matrix ρ σ ℂ) (c : ℂ) (F : MvPolynomial ρ ℂ) :
    a3m_scale (R := ℂ) c (a3r_lin ℓ F) = a3r_lin ℓ (a3m_scale (R := ℂ) c F) := by
  have : (a3m_scale (R := ℂ) (σ := σ) c).comp (a3r_lin ℓ) =
      (a3r_lin ℓ).comp (a3m_scale (R := ℂ) (σ := ρ) c) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have hs : ∀ {κ : Type} (k : κ), a3m_scale (R := ℂ) c (X k) = C c * X k := fun k => by
      simp [a3m_scale]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, a3r_lin_X, hs, map_mul, a3r_lin_C, a3r_lin_X,
      map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hs]
    have : a3m_scale (R := ℂ) (σ := σ) c (C (ℓ i k)) = C (ℓ i k) := by simp [a3m_scale]
    rw [this]
    ring
  exact congrArg (fun φ : MvPolynomial ρ ℂ →ₐ[ℂ] MvPolynomial σ ℂ => φ F) this

end Linear

/-! ## Extension of primes along a renaming -/

section Rename

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- The splitting `ℂ[x_σ] ≅ ℂ[y_ρ][x_τ]` for an injection `e : ρ → σ`, with `τ` the complement of
its range. -/
def a3r_splitEquiv (e : ρ → σ) (he : Function.Injective e) :
    MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial {k // k ∉ Set.range e} (MvPolynomial ρ ℂ) := by
  classical
  exact (renameEquiv ℂ ((Equiv.sumComm _ _).trans
      ((Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
        (Equiv.sumCompl (· ∈ Set.range e))))).symm.trans
    (sumAlgEquiv ℂ {k // k ∉ Set.range e} ρ)

omit [Fintype σ] in
theorem a3r_splitEquiv_rename (e : ρ → σ) (he : Function.Injective e) (F : MvPolynomial ρ ℂ) :
    a3r_splitEquiv e he (rename e F) = C F := by
  classical
  have : ((a3r_splitEquiv e he).toAlgHom.comp (rename e) : MvPolynomial ρ ℂ →ₐ[ℂ] _) =
      (IsScalarTower.toAlgHom ℂ (MvPolynomial ρ ℂ) (MvPolynomial {k // k ∉ Set.range e}
        (MvPolynomial ρ ℂ))) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, rename_X, IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq]
    change (sumAlgEquiv ℂ {k // k ∉ Set.range e} ρ) ((renameEquiv ℂ _).symm (X (e i))) = _
    rw [renameEquiv_symm, renameEquiv_apply, rename_X]
    have h1 : ((Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.ofInjective e he)
        (Equiv.refl {k // k ∉ Set.range e})).trans (Equiv.sumCompl (· ∈ Set.range e)))).symm (e i) =
        Sum.inr i := by
      rw [Equiv.symm_apply_eq]
      simp
    rw [h1, sumAlgEquiv_X_inr]
  exact congrArg (fun φ : MvPolynomial ρ ℂ →ₐ[ℂ] _ => φ F) this

/-- The extension of a prime along an injective renaming is prime, of dimension increased by the
number of new variables. -/
theorem a3r_map_rename_isPrime (e : ρ → σ) (he : Function.Injective e)
    (𝔭 : Ideal (MvPolynomial ρ ℂ)) [𝔭.IsPrime] :
    (Ideal.map (rename e) 𝔭).IsPrime ∧
      ringKrullDim (MvPolynomial σ ℂ ⧸ Ideal.map (rename e) 𝔭) =
        ringKrullDim (MvPolynomial ρ ℂ ⧸ 𝔭) + (Fintype.card σ - Fintype.card ρ : ℕ) := by
  classical
  let τ := {k // k ∉ Set.range e}
  let Φ : MvPolynomial σ ℂ ≃+* MvPolynomial τ (MvPolynomial ρ ℂ) :=
    (a3r_splitEquiv e he).toRingEquiv
  let r : MvPolynomial ρ ℂ →+* MvPolynomial σ ℂ := (rename e).toRingHom
  have hΦr : Φ.toRingHom.comp r = C := by
    refine RingHom.ext fun F => ?_
    exact a3r_splitEquiv_rename e he F
  have hmap : Ideal.map Φ.toRingHom (Ideal.map r 𝔭) = RingHom.ker
      (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk 𝔭)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_map, hΦr]
  have hsurj : Function.Surjective (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk 𝔭)) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  let e₁ : (MvPolynomial σ ℂ ⧸ Ideal.map r 𝔭) ≃+* MvPolynomial τ (MvPolynomial ρ ℂ ⧸ 𝔭) :=
    (Ideal.quotientEquiv _ _ Φ hmap.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hdom : IsDomain (MvPolynomial σ ℂ ⧸ Ideal.map r 𝔭) :=
    e₁.toMulEquiv.isDomain_iff.2 inferInstance
  refine ⟨(Ideal.Quotient.isDomain_iff_prime _).1 hdom, ?_⟩
  change ringKrullDim (MvPolynomial σ ℂ ⧸ Ideal.map r 𝔭) = _
  rw [ringKrullDim_eq_of_ringEquiv e₁, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ENat.card_eq_coe_fintype_card]
  congr 2
  rw [Fintype.card_subtype_compl, Set.card_range_of_injective he]

end Rename

/-! ## Cones over subvarieties with a linear vertex -/

section Cone

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

/-- The cone `ℓ⁻¹(ℓ(V(P)))` with vertex `V(ℓ)` over `V(P)`: the extension to `ℂ[x_σ]` of the
contraction of `P` to the subring `ℂ[ℓ_ρ]`. -/
def a3r_cone (ℓ : Matrix ρ σ ℂ) (P : Ideal (MvPolynomial σ ℂ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (a3r_lin ℓ) (Ideal.comap (a3r_lin ℓ) P)

omit [Fintype ρ] in
theorem a3r_cone_le (ℓ : Matrix ρ σ ℂ) (P : Ideal (MvPolynomial σ ℂ)) : a3r_cone ℓ P ≤ P :=
  Ideal.map_comap_le

/-- For a submatrix of an invertible matrix, the cone over a prime is prime, of dimension
`dim ℂ[ℓ]/(P ∩ ℂ[ℓ]) + card σ - card ρ`. -/
theorem a3r_cone_isPrime [DecidableEq σ] (g : Matrix σ σ ℂ) (hg : IsUnit g.det) (e : ρ → σ)
    (he : Function.Injective e) (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime] :
    (a3r_cone (g.submatrix e id) P).IsPrime ∧
      ringKrullDim (MvPolynomial σ ℂ ⧸ a3r_cone (g.submatrix e id) P) =
        ringKrullDim (MvPolynomial ρ ℂ ⧸ Ideal.comap (a3r_lin (g.submatrix e id)) P) +
          (Fintype.card σ - Fintype.card ρ : ℕ) := by
  set 𝔭 := Ideal.comap (a3r_lin (g.submatrix e id)) P
  have h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ P
  obtain ⟨hpr, hdim⟩ := a3r_map_rename_isPrime e he 𝔭
  let Ψ : MvPolynomial σ ℂ ≃+* MvPolynomial σ ℂ := (a3r_linEquiv g hg).toRingEquiv
  have hlin : ((a3r_lin (g.submatrix e id) : MvPolynomial ρ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) :
      MvPolynomial ρ ℂ →+* MvPolynomial σ ℂ) = Ψ.toRingHom.comp (rename (R := ℂ) e).toRingHom := by
    rw [a3r_lin_submatrix]
    rfl
  have hcone : a3r_cone (g.submatrix e id) P =
      Ideal.map Ψ.toRingHom (Ideal.map (rename (R := ℂ) e).toRingHom 𝔭) := by
    rw [Ideal.map_map, ← hlin, Ideal.map_coe]
    rfl
  rw [hcone]
  have : (Ideal.map (rename (R := ℂ) e).toRingHom 𝔭).IsPrime := hpr
  refine ⟨Ideal.map_isPrime_of_equiv Ψ, ?_⟩
  rw [← hdim]
  exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ Ψ rfl)).symm

omit [Fintype ρ] in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The cone over a homogeneous ideal is homogeneous. -/
theorem a3r_cone_isHomogeneous (ℓ : Matrix ρ σ ℂ) (P : Ideal (MvPolynomial σ ℂ))
    (hP : P.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    (a3r_cone ℓ P).IsHomogeneous (homogeneousSubmodule σ ℂ) := by
  refine a3m_isHomogeneous_of_scale _ fun c _ G hG => ?_
  have hle : a3r_cone ℓ P ≤ (a3r_cone ℓ P).comap (a3m_scale (R := ℂ) c) := by
    refine Ideal.map_le_iff_le_comap.2 fun F hF => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, a3r_lin_scale]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ← a3r_lin_scale]
    exact a3m_scale_mem_of_isHomogeneous hP c hF
  exact hle hG

end Cone

/-! ## Extending the linear forms to coordinates -/

section Extend

variable {n N : ℕ}

/-- The square matrix whose first `n + 1` rows are `ℓ` and whose other rows are the standard
basis vectors. -/
def a3r_ext (ℓ : Matrix (Fin (n + 1)) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun r k => if h : (r : ℕ) < n + 1 then ℓ ⟨r, h⟩ k else if r = k then 1 else 0

theorem a3r_ext_submatrix (hnN : n ≤ N) (ℓ : Matrix (Fin (n + 1)) (Fin (N + 1)) ℂ) :
    (a3r_ext ℓ).submatrix (Fin.castLE (by omega)) id = ℓ := by
  ext i k
  have : ((Fin.castLE (show n + 1 ≤ N + 1 by omega) i : Fin (N + 1)) : ℕ) < n + 1 := by
    simp [i.2]
  simp only [Matrix.submatrix_apply, id, a3r_ext, Matrix.of_apply, this]
  rfl

/-- The matrix of a parameter point. -/
def a3r_mat {ρ σ : Type} (a : ρ × σ → ℂ) : Matrix ρ σ ℂ := Matrix.of fun i k => a (i, k)

/-- For generic `ℓ`, the extended matrix is invertible. -/
theorem a3r_generic_ext_det :
    a3r_Generic {a : Fin (n + 1) × Fin (N + 1) → ℂ | IsUnit (a3r_ext (a3r_mat a)).det} := by
  classical
  let Pm : Matrix (Fin (N + 1)) (Fin (N + 1)) (MvPolynomial (Fin (n + 1) × Fin (N + 1)) ℂ) :=
    Matrix.of fun r k => if h : (r : ℕ) < n + 1 then X (⟨r, h⟩, k) else
      C (if r = k then 1 else 0)
  have heval : ∀ a, eval a Pm.det = (a3r_ext (a3r_mat a)).det := by
    intro a
    rw [RingHom.map_det]
    congr 1
    ext r k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Pm, a3r_ext, a3r_mat, Matrix.of_apply]
    split_ifs <;> simp_all
  refine ⟨Pm.det, fun h0 => ?_, fun a ha => ?_⟩
  · have := heval (fun ik => if (ik.1 : ℕ) = ik.2 then 1 else 0)
    rw [h0, map_zero] at this
    have hone : a3r_ext (a3r_mat (fun ik : Fin (n + 1) × Fin (N + 1) =>
        if (ik.1 : ℕ) = ik.2 then (1 : ℂ) else 0)) = 1 := by
      ext r k
      simp only [a3r_ext, a3r_mat, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
      split_ifs <;> rfl
    rw [hone, Matrix.det_one] at this
    exact one_ne_zero this.symm
  · rw [heval] at ha
    exact isUnit_iff_ne_zero.2 ha

end Extend

end HodgeLean.Adapters

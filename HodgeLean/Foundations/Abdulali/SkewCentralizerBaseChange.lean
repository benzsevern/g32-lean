import HodgeLean.Foundations.HodgeLieAlgebra
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- The complexification of a kernel, computed by a complex map compatible with the rational one
through an injective comparison map. -/
private theorem abd_complexSpan_ker {W : Type*} [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W] {M M' : Type*} [AddCommGroup M]
    [Module ℚ M] [AddCommGroup M'] [Module ℂ M'] (f : Module.End ℚ W →ₗ[ℚ] M)
    (g : Module.End ℂ (ℂ ⊗[ℚ] W) →ₗ[ℂ] M') (ψ : ℂ ⊗[ℚ] M →ₗ[ℂ] M') (hψ : Function.Injective ψ)
    (h : ∀ X, g (X.baseChange ℂ) = ψ (1 ⊗ₜ f X)) :
    complexSpan (LinearMap.ker f) = LinearMap.ker g := by
  have key : ∀ y, ψ (f.baseChange ℂ y) = g (endBaseChangeEquiv W y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul z X =>
      rw [LinearMap.baseChange_tmul, endBaseChangeEquiv_apply, tensorProductEnd_tmul, map_smul, h,
        ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  ext c
  rw [mem_complexSpan_iff, ← ker_baseChange_eq, LinearMap.mem_ker, LinearMap.mem_ker,
    ← hψ.eq_iff, map_zero, key, LinearEquiv.apply_symm_apply]

/-- The commutator map `X ↦ X T - T X`, over any field. -/
private abbrev abdCommMap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T : Module.End K W) : Module.End K W →ₗ[K] Module.End K W :=
  LinearMap.mulRight K T - LinearMap.mulLeft K T

private theorem abd_mem_ker_commMap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T X : Module.End K W) : X ∈ LinearMap.ker (abdCommMap T) ↔ X * T = T * X := by
  simp [abdCommMap, sub_eq_zero]

/-- The complexification of the commutant of a rational endomorphism is the commutant of its base
change. -/
private theorem abd_complexSpan_ker_commMap {W : Type*} [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W] (T : Module.End ℚ W) :
    complexSpan (LinearMap.ker (abdCommMap T)) = LinearMap.ker (abdCommMap (T.baseChange ℂ)) := by
  refine abd_complexSpan_ker _ _ (endBaseChangeEquiv W).toLinearMap
    (endBaseChangeEquiv W).injective fun X => ?_
  simp only [abdCommMap, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe, endBaseChangeEquiv_apply, tensorProductEnd_one_tmul,
    LinearMap.baseChange_sub, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- The rational skewness defect of `X` for `E` on the pairs of a finite basis. -/
private def abdSkewMapQ (E : LinearMap.BilinForm ℚ V) :
    Module.End ℚ V →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) where
  toFun X p := E (X (Module.finBasis ℚ V p.1)) (Module.finBasis ℚ V p.2) +
    E (Module.finBasis ℚ V p.1) (X (Module.finBasis ℚ V p.2))
  map_add' X Y := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z X := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

/-- The complex skewness defect of `c` for `E_ℂ` on the pairs `1 ⊗ bᵢ`. -/
private def abdSkewMapC (E : LinearMap.BilinForm ℚ V) :
    Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℂ) where
  toFun c p := E.baseChange ℂ (c (1 ⊗ₜ Module.finBasis ℚ V p.1)) (1 ⊗ₜ Module.finBasis ℚ V p.2) +
    E.baseChange ℂ (1 ⊗ₜ Module.finBasis ℚ V p.1) (c (1 ⊗ₜ Module.finBasis ℚ V p.2))
  map_add' c d := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z c := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

private theorem abd_mem_ker_skewMapQ (E : LinearMap.BilinForm ℚ V) (X : Module.End ℚ V) :
    X ∈ LinearMap.ker (abdSkewMapQ E) ↔ ∀ x y, E (X x) y = -E x (X y) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hB : E.compl₁₂ X LinearMap.id + E.compl₁₂ LinearMap.id X = 0 := by
      refine LinearMap.ext_basis (Module.finBasis ℚ V) (Module.finBasis ℚ V) fun k l => ?_
      have := congrFun h (k, l)
      simpa [abdSkewMapQ] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [abdSkewMapQ, h]

private theorem abd_mem_ker_skewMapC (E : LinearMap.BilinForm ℚ V)
    (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ LinearMap.ker (abdSkewMapC E) ↔
      ∀ x y, E.baseChange ℂ (c x) y = -E.baseChange ℂ x (c y) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hB : (E.baseChange ℂ).compl₁₂ c LinearMap.id +
        (E.baseChange ℂ).compl₁₂ LinearMap.id c = 0 := by
      refine LinearMap.ext_basis (Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V))
        (Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V)) fun k l => ?_
      have := congrFun h (k, l)
      simpa [Algebra.TensorProduct.basis_apply, abdSkewMapC] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [abdSkewMapC, h]

private theorem abd_complexSpan_ker_skewMap (E : LinearMap.BilinForm ℚ V) :
    complexSpan (LinearMap.ker (abdSkewMapQ E)) = LinearMap.ker (abdSkewMapC E) := by
  refine abd_complexSpan_ker _ _
    (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V))).toLinearMap
    (TensorProduct.piScalarRight ℚ ℂ ℂ _).injective fun X => ?_
  funext p
  simp [abdSkewMapC, abdSkewMapQ, TensorProduct.piScalarRightHom_tmul,
    LinearMap.BilinForm.baseChange_tmul, add_smul]


/-- The rational skew centralizer of a finite family of operators. It is
constructed as a finite system of linear equations.
Source: scalar-extension linear algebra underlying Abdulali, Annals of
Mathematics 155 (2002), §3.2 and §4. -/
def skewCentralizerOfFamily {k : ℕ} (E : LinearMap.BilinForm ℚ V)
    (F : Fin k → Module.End ℚ V) : Submodule ℚ (Module.End ℚ V) :=
  LinearMap.ker (abdSkewMapQ E) ⊓ ⨅ i, LinearMap.ker (abdCommMap (F i))

example {k : ℕ} (E : LinearMap.BilinForm ℚ V) (F : Fin k → Module.End ℚ V) :
    (0 : Module.End ℚ V) ∈ skewCentralizerOfFamily E F := Submodule.zero_mem _

/-- Membership in the finite-family skew centralizer is the stated skewness
and commutation system.
Source: scalar-extension linear algebra in Abdulali, Annals of Mathematics
155 (2002), §3.2 and §4. -/
theorem mem_skewCentralizerOfFamily {k : ℕ} (E : LinearMap.BilinForm ℚ V)
    (F : Fin k → Module.End ℚ V) (X : Module.End ℚ V) :
    X ∈ skewCentralizerOfFamily E F ↔
      (∀ z w, E (X z) w + E z (X w) = 0) ∧ ∀ i, X * F i = F i * X := by
  simp only [skewCentralizerOfFamily, Submodule.mem_inf, Submodule.mem_iInf,
    abd_mem_ker_skewMapQ, abd_mem_ker_commMap, eq_neg_iff_add_eq_zero]

private theorem complexSpan_iInf_fin (k : ℕ) (W : Fin k → Submodule ℚ (Module.End ℚ V)) :
    complexSpan (⨅ i, W i) = ⨅ i, complexSpan (W i) := by
  induction k with
  | zero => simp only [iInf_of_empty]; exact complexSpan_top
  | succ k ih =>
    have hQ : (⨅ i, W i) = W 0 ⊓ ⨅ i : Fin k, W i.succ := by
      ext x; simp [Fin.forall_fin_succ]
    rw [hQ, complexSpan_inf, ih]
    ext x; simp [Fin.forall_fin_succ]

/-- Extension of scalars retains the exact skew-centralizer equations for
any finite rational family. Both skewness and every commutator are retained,
with no additional trace equation.
Source: flat scalar extension of kernels, as used in Abdulali, Annals of
Mathematics 155 (2002), §3.2 and §4. -/
theorem skewCentralizerOfFamily_baseChange {k : ℕ} (E : LinearMap.BilinForm ℚ V)
    (F : Fin k → Module.End ℚ V) (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    X ∈ complexSpan (skewCentralizerOfFamily E F) ↔
      (∀ z w, E.baseChange ℂ (X z) w + E.baseChange ℂ z (X w) = 0) ∧
      ∀ i, X * (F i).baseChange ℂ = (F i).baseChange ℂ * X := by
  rw [skewCentralizerOfFamily, complexSpan_inf, complexSpan_iInf_fin,
    abd_complexSpan_ker_skewMap]
  simp only [abd_complexSpan_ker_commMap, Submodule.mem_inf, Submodule.mem_iInf,
    abd_mem_ker_skewMapC, abd_mem_ker_commMap, eq_neg_iff_add_eq_zero]

end HodgeLean.Foundations.Abdulali

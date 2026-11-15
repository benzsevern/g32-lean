import HodgeLean.Foundations.EQWCoreDefs

/-! # Proof obligations for the EQW stage 1 specification -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Foundations

open WeilPower
open scoped TensorProduct

section Bridge

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

/-- The complexification of a kernel, computed by a complex map compatible with the rational one
through an injective comparison map. -/
private theorem eqwA_complexSpan_ker {W : Type*} [AddCommGroup W] [Module ℚ W]
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
private abbrev eqwACommMap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T : Module.End K W) : Module.End K W →ₗ[K] Module.End K W :=
  LinearMap.mulRight K T - LinearMap.mulLeft K T

private theorem eqwA_mem_ker_commMap {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T X : Module.End K W) : X ∈ LinearMap.ker (eqwACommMap T) ↔ X * T = T * X := by
  simp [eqwACommMap, sub_eq_zero]

/-- The complexification of the commutant of a rational endomorphism is the commutant of its base
change. -/
private theorem eqwA_complexSpan_ker_commMap {W : Type*} [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W] (T : Module.End ℚ W) :
    complexSpan (LinearMap.ker (eqwACommMap T)) = LinearMap.ker (eqwACommMap (T.baseChange ℂ)) := by
  refine eqwA_complexSpan_ker _ _ (endBaseChangeEquiv W).toLinearMap
    (endBaseChangeEquiv W).injective fun X => ?_
  simp only [eqwACommMap, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe, endBaseChangeEquiv_apply, tensorProductEnd_one_tmul,
    LinearMap.baseChange_sub, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- The rational centralizer of `T`, as a Lie subalgebra. -/
private def eqwACentralizerLie (T : Module.End ℚ V) : LieSubalgebra ℚ (Module.End ℚ V) where
  toSubmodule := LinearMap.ker (eqwACommMap T)
  lie_mem' := by
    intro X Y hX hY
    have hX' := (eqwA_mem_ker_commMap T X).mp hX
    have hY' := (eqwA_mem_ker_commMap T Y).mp hY
    refine (eqwA_mem_ker_commMap T _).mpr ?_
    rw [Ring.lie_def, sub_mul, mul_sub, mul_assoc X Y T, hY', ← mul_assoc X T Y, hX',
      mul_assoc T X Y, mul_assoc Y X T, hX', ← mul_assoc Y T X, hY', mul_assoc T Y X]

theorem spec_eqw_mem_centralizer_hodgeLieAlgebra_iff_aux (T : Module.End ℚ V) :
    T ∈ Subalgebra.centralizer ℚ (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) ↔
      T.baseChange ℂ * gradingOperator H hH = gradingOperator H hH * T.baseChange ℂ := by
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro hT
    have hC := gradingOperator_mem_span_hodgeLieAlgebra H hH
    have hle : Submodule.span ℂ ((fun X : Module.End ℚ V => X.baseChange ℂ) ''
        ((hodgeLieAlgebra H hH).toSubmodule : Set _)) ≤
        LinearMap.ker (eqwACommMap (T.baseChange ℂ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨X, hX, rfl⟩
      rw [SetLike.mem_coe, eqwA_mem_ker_commMap]
      have h := congrArg (LinearMap.baseChange ℂ) (hT X hX)
      simpa only [Module.End.mul_eq_comp, LinearMap.baseChange_comp] using h
    exact ((eqwA_mem_ker_commMap _ _).mp (hle hC)).symm
  · intro hT X hX
    have hC : gradingOperator H hH ∈ complexSpan (eqwACentralizerLie T).toSubmodule := by
      change gradingOperator H hH ∈ complexSpan (LinearMap.ker (eqwACommMap T))
      rw [eqwA_complexSpan_ker_commMap, eqwA_mem_ker_commMap]
      exact hT.symm
    exact (eqwA_mem_ker_commMap T X).mp (hodgeLieAlgebra_le H hH hC hX)

theorem spec_eqw_gradingOperator_mul_self_aux
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥) :
    gradingOperator H hH * gradingOperator H hH = -1 := by
  classical
  refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
  obtain ⟨p, q⟩ := pq
  rw [Module.End.mul_apply, gradingOperator_apply_of_mem H hH hx, map_smul,
    gradingOperator_apply_of_mem H hH hx, smul_smul, LinearMap.neg_apply, Module.End.one_apply]
  by_cases h10 : (p, q) = (1, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h10
    rw [← neg_one_smul ℂ x]
    congr 1
    push_cast
    ring_nf
    simp
  by_cases h01 : (p, q) = (0, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h01
    rw [← neg_one_smul ℂ x]
    congr 1
    push_cast
    ring_nf
    simp
  rw [hsupp _ h10 h01, Submodule.mem_bot] at hx
  simp [hx]

end Bridge

section WeilSU

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- The rational skewness defect of `X` for `E` on the pairs of a finite basis. -/
private def eqwASkewMapQ (E : LinearMap.BilinForm ℚ V) :
    Module.End ℚ V →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) where
  toFun X p := E (X (Module.finBasis ℚ V p.1)) (Module.finBasis ℚ V p.2) +
    E (Module.finBasis ℚ V p.1) (X (Module.finBasis ℚ V p.2))
  map_add' X Y := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z X := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

/-- The complex skewness defect of `c` for `E_ℂ` on the pairs `1 ⊗ bᵢ`. -/
private def eqwASkewMapC (E : LinearMap.BilinForm ℚ V) :
    Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℂ) where
  toFun c p := E.baseChange ℂ (c (1 ⊗ₜ Module.finBasis ℚ V p.1)) (1 ⊗ₜ Module.finBasis ℚ V p.2) +
    E.baseChange ℂ (1 ⊗ₜ Module.finBasis ℚ V p.1) (c (1 ⊗ₜ Module.finBasis ℚ V p.2))
  map_add' c d := by funext p; simp only [LinearMap.add_apply, map_add, Pi.add_apply]; ring
  map_smul' z c := by
    funext p; simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

private theorem eqwA_mem_ker_skewMapQ (E : LinearMap.BilinForm ℚ V) (X : Module.End ℚ V) :
    X ∈ LinearMap.ker (eqwASkewMapQ E) ↔ ∀ x y, E (X x) y = -E x (X y) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hB : E.compl₁₂ X LinearMap.id + E.compl₁₂ LinearMap.id X = 0 := by
      refine LinearMap.ext_basis (Module.finBasis ℚ V) (Module.finBasis ℚ V) fun k l => ?_
      have := congrFun h (k, l)
      simpa [eqwASkewMapQ] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [eqwASkewMapQ, h]

private theorem eqwA_mem_ker_skewMapC (E : LinearMap.BilinForm ℚ V)
    (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ LinearMap.ker (eqwASkewMapC E) ↔
      ∀ x y, E.baseChange ℂ (c x) y = -E.baseChange ℂ x (c y) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hB : (E.baseChange ℂ).compl₁₂ c LinearMap.id +
        (E.baseChange ℂ).compl₁₂ LinearMap.id c = 0 := by
      refine LinearMap.ext_basis (Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V))
        (Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V)) fun k l => ?_
      have := congrFun h (k, l)
      simpa [Algebra.TensorProduct.basis_apply, eqwASkewMapC] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [eqwASkewMapC, h]

private theorem eqwA_complexSpan_ker_skewMap (E : LinearMap.BilinForm ℚ V) :
    complexSpan (LinearMap.ker (eqwASkewMapQ E)) = LinearMap.ker (eqwASkewMapC E) := by
  refine eqwA_complexSpan_ker _ _
    (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V))).toLinearMap
    (TensorProduct.piScalarRight ℚ ℂ ℂ _).injective fun X => ?_
  funext p
  simp [eqwASkewMapC, eqwASkewMapQ, TensorProduct.piScalarRightHom_tmul,
    LinearMap.BilinForm.baseChange_tmul, add_smul]

/-- The complexification of the kernel of a rational trace functional `X ↦ tr (A X)`. -/
private theorem eqwA_complexSpan_ker_trace (A : Module.End ℚ V) :
    complexSpan (LinearMap.ker (LinearMap.trace ℚ V ∘ₗ LinearMap.mulLeft ℚ A)) =
      LinearMap.ker (LinearMap.trace ℂ (ℂ ⊗[ℚ] V) ∘ₗ LinearMap.mulLeft ℂ (A.baseChange ℂ)) := by
  refine eqwA_complexSpan_ker _ _ (TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ).toLinearMap
    (TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ).injective fun X => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul, Module.End.mul_eq_comp,
    ← LinearMap.baseChange_comp, LinearMap.trace_baseChange, Algebra.algebraMap_eq_smul_one]

private theorem eqwA_weilSU_eq_inf (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) :
    (weilSU E J).toSubmodule = LinearMap.ker (eqwACommMap J) ⊓ LinearMap.ker (eqwASkewMapQ E) ⊓
      LinearMap.ker (LinearMap.trace ℚ V ∘ₗ LinearMap.mulLeft ℚ 1) ⊓
      LinearMap.ker (LinearMap.trace ℚ V ∘ₗ LinearMap.mulLeft ℚ J) := by
  ext X
  simp only [Submodule.mem_inf]
  rw [eqwA_mem_ker_commMap, eqwA_mem_ker_skewMapQ, LinearMap.mem_ker, LinearMap.mem_ker]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, one_mul]
  change (X * J = J * X ∧ (∀ x y, E (X x) y = -E x (X y)) ∧
    LinearMap.trace ℚ V X = 0 ∧ LinearMap.trace ℚ V (J * X) = 0) ↔ _
  tauto

theorem spec_eqw_mem_complexSpan_weilSU_iff_aux (E : LinearMap.BilinForm ℚ V)
    (J : Module.End ℚ V) (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ complexSpan (weilSU E J).toSubmodule ↔
      c * J.baseChange ℂ = J.baseChange ℂ * c ∧
      (∀ x y, E.baseChange ℂ (c x) y = -E.baseChange ℂ x (c y)) ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) c = 0 ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) (J.baseChange ℂ * c) = 0 := by
  rw [eqwA_weilSU_eq_inf, complexSpan_inf, complexSpan_inf, complexSpan_inf,
    eqwA_complexSpan_ker_commMap, eqwA_complexSpan_ker_skewMap, eqwA_complexSpan_ker_trace,
    eqwA_complexSpan_ker_trace]
  simp only [Submodule.mem_inf]
  rw [eqwA_mem_ker_commMap, eqwA_mem_ker_skewMapC, LinearMap.mem_ker, LinearMap.mem_ker]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, LinearMap.baseChange_one,
    one_mul, and_assoc]

/-- In split coordinates, a block endomorphism `f ⊕ (-fᵀ)` has trace zero, and composed with the
split Weil operator it has trace `2 √-3 tr f`. -/
private theorem eqwA_trace_blockLie (W : Type*) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) :
    LinearMap.trace ℂ _ (blockLie W f) = 0 ∧
      LinearMap.trace ℂ _ (splitJ W * blockLie W f) = (2 * root) * LinearMap.trace ℂ W f := by
  have hd : LinearMap.trace ℂ _ (SchurWeyl.dualLie ℂ W f) = -LinearMap.trace ℂ W f := by
    rw [SchurWeyl.dualLie_apply, map_neg]
    congr 1
    exact LinearMap.trace_transpose' f
  constructor
  · change LinearMap.trace ℂ _ (f.prodMap (SchurWeyl.dualLie ℂ W f)) = 0
    rw [LinearMap.trace_prodMap', hd, add_neg_cancel]
  · have h : splitJ W * blockLie W f = (root • f).prodMap (-root • SchurWeyl.dualLie ℂ W f) := by
      ext x <;> simp [splitJ, blockLie]
    rw [h, LinearMap.trace_prodMap', map_smul, map_smul, hd, smul_eq_mul, smul_eq_mul]
    ring

theorem spec_eqw_complexSpan_weilSU_eq_complexSU_aux (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt) (J : Module.End ℚ V)
    (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    complexSpan (weilSU E J).toSubmodule = (complexSU E hE J hJ hskew).toSubmodule := by
  ext c
  rw [spec_eqw_mem_complexSpan_weilSU_iff_aux, LieSubalgebra.mem_toSubmodule,
    mem_complexSU E hE J hJ hskew hAlt, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  refine and_congr_right fun hc => and_congr_right fun hs => ?_
  let e := polarizedSplitting E hE J hJ hskew
  have hJmodel : e.conj (J.baseChange ℂ) = splitJ _ := by
    apply LinearMap.ext
    intro z
    simpa [e] using polarizedSplitting_J E hE J hJ hskew (e.symm z)
  have hc' : (e.conj c).comp (splitJ _) = (splitJ _).comp (e.conj c) := by
    rw [← hJmodel, ← e.conj_comp, ← e.conj_comp, ← Module.End.mul_eq_comp,
      ← Module.End.mul_eq_comp, hc]
  have hs' : ∀ x y, splitForm _ (e.conj c x) y = -splitForm _ x (e.conj c y) := by
    intro x y
    have h := hs (e.symm x) (e.symm y)
    simpa [polarizedSplitting_form E hE J hJ hskew hAlt, e] using h
  have hblock := eq_blockLie_of_commutes_skew _ (e.conj c) hc' hs'
  have htr : LinearMap.trace ℂ (ℂ ⊗[ℚ] V) c = LinearMap.trace ℂ _ (e.conj c) :=
    (LinearMap.trace_conj' c e).symm
  have htrJ : LinearMap.trace ℂ (ℂ ⊗[ℚ] V) (J.baseChange ℂ * c) =
      LinearMap.trace ℂ _ (splitJ _ * e.conj c) := by
    rw [← LinearMap.trace_conj' _ e, Module.End.mul_eq_comp, e.conj_comp, hJmodel]
    rfl
  obtain ⟨h1, h2⟩ := eqwA_trace_blockLie _ (firstBlock _ (e.conj c))
  rw [hblock] at htr htrJ
  rw [htr, htrJ, h1, h2]
  have h2r : (2 * root) ≠ 0 := mul_ne_zero two_ne_zero root_ne_zero
  constructor
  · rintro ⟨-, h⟩
    exact (mul_eq_zero.mp h).resolve_left h2r
  · intro h
    exact ⟨rfl, by rw [h, mul_zero]⟩

variable {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

omit [FiniteDimensional ℚ V] in
theorem eqwB_isProj_mul {M : Type*} [AddCommGroup M] [Module ℂ M] {A B : Submodule ℂ M}
    {p q : Module.End ℂ M} (hp : LinearMap.IsProj A p) (hq : LinearMap.IsProj B q)
    (hc : p * q = q * p) : LinearMap.IsProj (A ⊓ B) (p * q) := by
  refine ⟨fun x => ⟨hp.map_mem _, ?_⟩, fun x hx => ?_⟩
  · rw [hc]; exact hq.map_mem _
  · rw [Module.End.mul_apply, hq.map_id x hx.2, hp.map_id x hx.1]

theorem spec_eqw_hodgeLieAlgebra_le_weilSU_aux {d : ℚ} (hd : 0 < d) (μ : ℂ)
    (hμ : μ * μ = -(d : ℂ)) (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id)
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ H pq, J.baseChange ℂ x ∈ H pq)
    (hiso₁₀ : ∀ x ∈ H (1, 0), ∀ y ∈ H (1, 0), E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ H (0, 1), ∀ y ∈ H (0, 1), E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ))
    (hbalNeg : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-μ)) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-μ))) :
    hodgeLieAlgebra H hH ≤ weilSU E J := by
  classical
  set C := gradingOperator H hH with hCdef
  set Jc := J.baseChange ℂ with hJcdef
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have : (d : ℂ) = 0 := by simpa using hμ
    exact hd.ne' (by exact_mod_cast this)
  have hJJ : ∀ w, Jc (Jc w) = (μ * μ) • w := by
    intro w
    rw [hJcdef, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hJ, hμ]
    induction w using TensorProduct.inductionOn with
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Rat.cast_smul_eq_qsmul ℂ]
      simp only [smul_eq_mul, Rat.cast_neg, neg_mul, TensorProduct.neg_tmul, neg_smul,
        TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  have hdec : ∀ y, ∃ y₁ ∈ H (1, 0), ∃ y₂ ∈ H (0, 1), y₁ + y₂ = y := by
    intro y
    have hy : y ∈ H (1, 0) ⊔ H (0, 1) := by
      have : y ∈ ⨆ pq, H pq := by rw [hH.submodule_iSup_eq_top]; trivial
      refine (iSup_le (fun pq => ?_) : ⨆ pq, H pq ≤ H (1, 0) ⊔ H (0, 1)) this
      by_cases h1 : pq = (1, 0)
      · subst h1; exact le_sup_left
      by_cases h2 : pq = (0, 1)
      · subst h2; exact le_sup_right
      rw [hsupp pq h1 h2]; exact bot_le
    exact Submodule.mem_sup.mp hy
  have hC10 : ∀ x ∈ H (1, 0), C x = Complex.I • x := fun x hx => by
    rw [hCdef, gradingOperator_apply_of_mem H hH hx]; simp
  have hC01 : ∀ x ∈ H (0, 1), C x = (-Complex.I) • x := fun x hx => by
    rw [hCdef, gradingOperator_apply_of_mem H hH hx]; simp
  have hCJ : C * Jc = Jc * C := by
    refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
    obtain ⟨p, q⟩ := pq
    rw [Module.End.mul_apply, Module.End.mul_apply, hCdef,
      gradingOperator_apply_of_mem H hH (hJH _ x hx), gradingOperator_apply_of_mem H hH hx,
      map_smul]
  have hskewC : ∀ x y, E.baseChange ℂ (C x) y = -E.baseChange ℂ x (C y) := by
    intro x y
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hdec x
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hdec y
    simp only [map_add, LinearMap.add_apply, hC10 _ hx₁, hC01 _ hx₂, hC10 _ hy₁, hC01 _ hy₂,
      map_smul, LinearMap.smul_apply, hiso₁₀ _ hx₁ _ hy₁, hiso₀₁ _ hx₂ _ hy₂, smul_eq_mul]
    ring
  set P : Module.End ℂ (ℂ ⊗[ℚ] V) := (1 / 2 : ℂ) • (1 - Complex.I • C) with hPdef
  set Q : Module.End ℂ (ℂ ⊗[ℚ] V) := (1 / 2 : ℂ) • (1 + μ⁻¹ • Jc) with hQdef
  have hPy : ∀ y₁ ∈ H (1, 0), ∀ y₂ ∈ H (0, 1), P (y₁ + y₂) = y₁ := by
    intro y₁ hy₁ y₂ hy₂
    simp only [hPdef, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_add,
      hC10 _ hy₁, hC01 _ hy₂]
    simp only [smul_smul, Complex.I_mul_I, mul_neg, neg_neg]
    module
  have hP10 : LinearMap.IsProj (H (1, 0)) P := by
    refine ⟨fun y => ?_, fun x hx => ?_⟩
    · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hdec y
      rw [hPy y₁ hy₁ y₂ hy₂]; exact hy₁
    · simpa using hPy x hx 0 (zero_mem _)
  have hP01 : LinearMap.IsProj (H (0, 1)) (1 - P) := by
    refine ⟨fun y => ?_, fun x hx => ?_⟩
    · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hdec y
      rw [LinearMap.sub_apply, hPy y₁ hy₁ y₂ hy₂, Module.End.one_apply, add_sub_cancel_left]
      exact hy₂
    · have := hPy 0 (zero_mem _) x hx
      rw [zero_add] at this
      rw [LinearMap.sub_apply, this, Module.End.one_apply, sub_zero]
  have hQp : LinearMap.IsProj (Module.End.eigenspace Jc μ) Q := by
    refine ⟨fun w => ?_, fun x hx => ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      simp only [hQdef, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
        map_smul, map_add, hJJ, smul_smul]
      rw [show μ⁻¹ * (μ * μ) = μ by field_simp]
      match_scalars <;> field_simp
    · rw [Module.End.mem_eigenspace_iff] at hx
      simp only [hQdef, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, hx,
        smul_smul]
      rw [inv_mul_cancel₀ hμ0]
      module
  have hQm : LinearMap.IsProj (Module.End.eigenspace Jc (-μ)) (1 - Q) := by
    refine ⟨fun w => ?_, fun x hx => ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      simp only [hQdef, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
        Module.End.one_apply, map_smul, map_add, map_sub, hJJ, smul_smul]
      rw [show μ⁻¹ * (μ * μ) = μ by field_simp]
      match_scalars <;> field_simp <;> ring
    · rw [Module.End.mem_eigenspace_iff] at hx
      simp only [hQdef, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
        Module.End.one_apply, hx, smul_smul]
      rw [mul_neg, inv_mul_cancel₀ hμ0]
      module
  have hPQ : P * Q = Q * P := by
    simp only [hPdef, hQdef, sub_mul, mul_sub, add_mul, mul_add, one_mul,
      mul_one, smul_mul_assoc, mul_smul_comm, hCJ]
    module
  have h1PQ : (1 - P) * Q = Q * (1 - P) := by
    rw [sub_mul, mul_sub, hPQ, one_mul, mul_one]
  have hP1Q : P * (1 - Q) = (1 - Q) * P := by
    rw [sub_mul, mul_sub, hPQ, one_mul, mul_one]
  have h1P1Q : (1 - P) * (1 - Q) = (1 - Q) * (1 - P) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPQ]
    abel
  have t1 := (eqwB_isProj_mul hP10 hQp hPQ).trace
  have t2 := (eqwB_isProj_mul hP01 hQp h1PQ).trace
  have t3 := (eqwB_isProj_mul hP10 hQm hP1Q).trace
  have t4 := (eqwB_isProj_mul hP01 hQm h1P1Q).trace
  rw [← hbalPos] at t2
  rw [← hbalNeg] at t4
  simp only [sub_mul, mul_sub, one_mul, mul_one, map_sub, LinearMap.trace_one] at t2 t3 t4
  have hCP : C = Complex.I • ((2 : ℂ) • P - 1) := by
    rw [hPdef]
    simp only [smul_sub, smul_smul]
    match_scalars <;> ring_nf
    simp only [Complex.I_sq]
    ring
  have hJQ : Jc = μ • ((2 : ℂ) • Q - 1) := by
    rw [hQdef]
    simp only [smul_add, smul_sub, smul_smul]
    match_scalars <;> simp [hμ0]
  apply hodgeLieAlgebra_le
  refine (spec_eqw_mem_complexSpan_weilSU_iff_aux E J C).mpr ⟨hCJ, hskewC, ?_, ?_⟩
  · rw [hCP, map_smul, map_sub, map_smul, LinearMap.trace_one, smul_eq_mul, smul_eq_mul]
    linear_combination (-Complex.I) * (t4 - t3 + t2 - t1)
  · rw [← hJcdef, hJQ, hCP]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, map_smul, map_sub, LinearMap.trace_one, smul_eq_mul, ← hPQ]
    linear_combination (Complex.I * μ) * (t4 - t3 - t2 + t1)

end WeilSU

section PartsAC

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

omit [FiniteDimensional ℚ V] in
theorem eqwB_mem_adjoin {d : ℚ} {J : Module.End ℚ V} (hJ : J.comp J = (-d) • LinearMap.id)
    {z : Module.End ℚ V} (hz : z ∈ Algebra.adjoin ℚ {J}) : ∃ a b : ℚ, z = a • 1 + b • J := by
  have hJJ : J * J = (-d) • (1 : Module.End ℚ V) := hJ
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by module⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    refine ⟨a * a' - d * b * b', a * b' + b * a', ?_⟩
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJJ, smul_smul]
    module

theorem spec_eqw_center_eq_bot_aux
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (hL : L ≤ weilSU E J)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J}) :
    LieAlgebra.center ℚ L = ⊥ := by
  have hJJ : J * J = (-d) • (1 : Module.End ℚ V) := hJ
  rw [eq_bot_iff]
  intro z hz
  rw [LieSubmodule.mem_bot]
  have hzc : (z : Module.End ℚ V) ∈ Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    have h := hz ⟨g, hg⟩
    rw [← sub_eq_zero]
    have h' := congrArg Subtype.val h
    simpa [LieSubalgebra.coe_bracket, Ring.lie_def] using h'
  rw [hcomm] at hzc
  obtain ⟨a, b, hab⟩ := eqwB_mem_adjoin hJ hzc
  obtain ⟨-, hsk, -, htr⟩ := hL z.2
  have hpos : 0 < Module.finrank ℚ V := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have ha : a = 0 := by
    by_contra ha
    apply hx
    apply hE.1 x
    intro y
    have h := hsk x y
    rw [hab] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, hskew, smul_eq_mul] at h
    have h2 : (2 * a) * E x y = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (by linarith : a = 0) ha
    · exact h3
  have hb : b = 0 := by
    rw [hab, ha, zero_smul, zero_add, mul_smul_comm, hJJ, map_smul, map_smul,
      LinearMap.trace_one] at htr
    simp only [smul_eq_mul] at htr
    have : (Module.finrank ℚ V : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    rcases mul_eq_zero.mp htr with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by linarith)
      · exact absurd h this
  apply Subtype.ext
  rw [hab, ha, hb]
  simp

theorem spec_eqw_hasTrivialRadical_aux
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (hL : L ≤ weilSU E J)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J})
    (hred : LieAlgebra.radical ℚ L = LieAlgebra.center ℚ L) :
    LieAlgebra.HasTrivialRadical ℚ L :=
  ⟨hred.trans (spec_eqw_center_eq_bot_aux hdim hd E hE J hJ hskew L hL hcomm)⟩

omit [FiniteDimensional ℚ V] in
/-- Rational slice of a complex vector along a `ℚ`-linear functional on `ℂ`. -/
theorem eqwB_slice_tmul (φ : ℂ →ₗ[ℚ] ℚ) (c : ℂ) (v : V) :
    (TensorProduct.lid ℚ V) (φ.rTensor V (c ⊗ₜ v)) = φ c • v := by
  simp

omit [FiniteDimensional ℚ V] in
theorem eqwB_eq_zero_of_slices {w : ℂ ⊗[ℚ] V}
    (h : ∀ φ : ℂ →ₗ[ℚ] ℚ, (TensorProduct.lid ℚ V) (φ.rTensor V w) = 0) : w = 0 := by
  let b := Module.Free.chooseBasis ℚ ℂ
  let e : ℂ ⊗[ℚ] V ≃ₗ[ℚ] _ :=
    (LinearEquiv.rTensor V b.repr).trans (TensorProduct.finsuppScalarLeft ℚ V _)
  have he : ∀ k (w : ℂ ⊗[ℚ] V), e w k = (TensorProduct.lid ℚ V) ((b.coord k).rTensor V w) := by
    intro k w
    induction w using TensorProduct.inductionOn with
    | tmul c v => simp [e, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply e.injective
  ext k
  rw [he, h, map_zero, Finsupp.zero_apply]

omit [FiniteDimensional ℚ V] in
theorem eqwB_baseChange_slice (φ : ℂ →ₗ[ℚ] ℚ) (X : Module.End ℚ V) (w : ℂ ⊗[ℚ] V) :
    (TensorProduct.lid ℚ V) (φ.rTensor V (X.baseChange ℂ w)) =
      X ((TensorProduct.lid ℚ V) (φ.rTensor V w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul c v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit [FiniteDimensional ℚ V] in
theorem eqwB_commute_J {d : ℚ} (J : Module.End ℚ V) (hJ : J.comp J = (-d) • LinearMap.id)
    (L : LieSubalgebra ℚ (Module.End ℚ V))
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J})
    (Φ : Module.End ℂ (ℂ ⊗[ℚ] V)) (hΦ : ∀ X ∈ L, Φ * X.baseChange ℂ = X.baseChange ℂ * Φ) :
    Φ * J.baseChange ℂ = J.baseChange ℂ * Φ := by
  have key : ∀ v : V, (Φ * J.baseChange ℂ - J.baseChange ℂ * Φ) (1 ⊗ₜ v) = 0 := by
    intro v
    apply eqwB_eq_zero_of_slices
    intro φ
    let Ψ : Module.End ℚ V := (TensorProduct.lid ℚ V).toLinearMap ∘ₗ φ.rTensor V ∘ₗ
      Φ.restrictScalars ℚ ∘ₗ TensorProduct.mk ℚ ℂ V 1
    have hΨ : Ψ ∈ Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro X hX
      ext u
      have h := congrArg (fun f => f (1 ⊗ₜ[ℚ] u)) (hΦ X hX)
      simp only [Module.End.mul_apply, LinearMap.baseChange_tmul] at h
      simp only [Ψ, Module.End.mul_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, h, eqwB_baseChange_slice]
    rw [hcomm] at hΨ
    obtain ⟨a, b, hab⟩ := eqwB_mem_adjoin hJ hΨ
    have hΨJ : Ψ * J = J * Ψ := by
      rw [hab]; simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have h := congrArg (fun f => f v) hΨJ
    simp only [Ψ, Module.End.mul_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at h
    rw [LinearMap.sub_apply, map_sub, map_sub, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.baseChange_tmul, eqwB_baseChange_slice, h, sub_self]
  rw [← sub_eq_zero]
  ext v
  simpa using key v

theorem spec_eqw_not_hasPlusMinusIntertwiner_aux
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (J : Module.End ℚ V) (hJ : J.comp J = (-d) • LinearMap.id) (μ : ℂ)
    (hμ : μ * μ = -(d : ℂ)) (L : LieSubalgebra ℚ (Module.End ℚ V))
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J}) :
    ¬ HasPlusMinusIntertwiner L J μ := by
  rintro ⟨Φ, hΦ0, hΦL, hpos, hneg⟩
  have hJΦ := eqwB_commute_J J hJ L hcomm Φ hΦL
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have : (d : ℂ) = 0 := by simpa using hμ
    exact hd.ne' (by exact_mod_cast this)
  have hJJ : ∀ w, J.baseChange ℂ (J.baseChange ℂ w) = (μ * μ) • w := by
    intro w
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hJ, hμ]
    induction w using TensorProduct.inductionOn with
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Rat.cast_smul_eq_qsmul ℂ]
      simp only [smul_eq_mul, Rat.cast_neg, neg_mul, TensorProduct.neg_tmul, neg_smul,
        TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  apply hΦ0
  refine LinearMap.ext fun w => ?_
  have hw : w = ((1 / 2 : ℂ) • (w + μ⁻¹ • J.baseChange ℂ w)) +
      ((1 / 2 : ℂ) • (w - μ⁻¹ • J.baseChange ℂ w)) := by module
  have hp : (1 / 2 : ℂ) • (w + μ⁻¹ • J.baseChange ℂ w) ∈
      Module.End.eigenspace (J.baseChange ℂ) μ := by
    rw [Module.End.mem_eigenspace_iff, map_smul, map_add, map_smul, hJJ, smul_smul]
    rw [show μ⁻¹ * (μ * μ) = μ by field_simp]
    match_scalars <;> field_simp
  have hm : (1 / 2 : ℂ) • (w - μ⁻¹ • J.baseChange ℂ w) ∈
      Module.End.eigenspace (J.baseChange ℂ) (-μ) := by
    rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, map_smul, hJJ, smul_smul]
    rw [show μ⁻¹ * (μ * μ) = μ by field_simp]
    match_scalars <;> field_simp
  set u := (1 / 2 : ℂ) • (w + μ⁻¹ • J.baseChange ℂ w)
  have hu : Φ u = 0 := by
    have h1 := Module.End.mem_eigenspace_iff.mp (hpos u hp)
    have h2 : J.baseChange ℂ (Φ u) = μ • Φ u := by
      rw [← Module.End.mul_apply, ← hJΦ, Module.End.mul_apply,
        Module.End.mem_eigenspace_iff.mp hp, map_smul]
    rw [h2] at h1
    have h3 : (2 * μ) • Φ u = 0 := by
      rw [two_mul, add_smul]; nth_rw 2 [h1]; simp
    exact (smul_eq_zero.mp h3).resolve_left (mul_ne_zero two_ne_zero hμ0)
  rw [hw, map_add, hu, hneg _ hm, add_zero, LinearMap.zero_apply]

end PartsAC

section Tensor

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

/-- Over a field, a pure tensor of nonzero vectors is nonzero. -/
theorem eqw_tmul_ne_zero {v : W₁} {w : W₂} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[ℂ] w ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W₁, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℂ W₂, ψ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
  intro h
  have := congrArg (fun t => TensorProduct.lid ℂ ℂ (TensorProduct.map φ ψ t)) h
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul, map_zero] at this
  exact mul_ne_zero hφ hψ this

/-- Eigenvalues add on pure tensors of eigenvectors. -/
theorem eqw_hasEigenvalue_tensor (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂) {μ ν : ℂ}
    (hμ : f₁.HasEigenvalue μ) (hν : f₂.HasEigenvalue ν) :
    Module.End.HasEigenvalue
      (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) (μ + ν) := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  obtain ⟨w, hw⟩ := hν.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v ⊗ₜ w) ⟨?_, eqw_tmul_ne_zero hv.2 hw.2⟩
  rw [Module.End.mem_eigenspace_iff]
  simp only [LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    Module.End.mem_eigenspace_iff.mp hv.1, Module.End.mem_eigenspace_iff.mp hw.1,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]

theorem spec_eqw_tensor_three_eigenvalues_aux (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂)
    {μ₁ ν₁ μ₂ ν₂ : ℂ} (hμ₁ : f₁.HasEigenvalue μ₁) (hν₁ : f₁.HasEigenvalue ν₁) (h₁ : μ₁ ≠ ν₁)
    (hμ₂ : f₂.HasEigenvalue μ₂) (hν₂ : f₂.HasEigenvalue ν₂) (h₂ : μ₂ ≠ ν₂) :
    ∃ a b c : ℂ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) a ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) b ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) c := by
  have h₁' : μ₁ - ν₁ ≠ 0 := sub_ne_zero.mpr h₁
  have h₂' : μ₂ - ν₂ ≠ 0 := sub_ne_zero.mpr h₂
  by_cases hc : ν₁ + μ₂ = μ₁ + ν₂
  · refine ⟨μ₁ + μ₂, μ₁ + ν₂, ν₁ + ν₂, ?_, ?_, ?_, eqw_hasEigenvalue_tensor f₁ f₂ hμ₁ hμ₂,
      eqw_hasEigenvalue_tensor f₁ f₂ hμ₁ hν₂, eqw_hasEigenvalue_tensor f₁ f₂ hν₁ hν₂⟩
    · intro h; exact h₂' (by linear_combination h)
    · intro h
      have : (2 : ℂ) * (μ₂ - ν₂) = 0 := by linear_combination h + hc
      exact h₂' ((mul_eq_zero.mp this).resolve_left two_ne_zero)
    · intro h; exact h₁' (by linear_combination h)
  · refine ⟨μ₁ + μ₂, μ₁ + ν₂, ν₁ + μ₂, ?_, ?_, fun h => hc h.symm,
      eqw_hasEigenvalue_tensor f₁ f₂ hμ₁ hμ₂, eqw_hasEigenvalue_tensor f₁ f₂ hμ₁ hν₂,
      eqw_hasEigenvalue_tensor f₁ f₂ hν₁ hμ₂⟩
    · intro h; exact h₂' (by linear_combination h)
    · intro h; exact h₁' (by linear_combination h)

/-- A nonzero traceless semisimple endomorphism has two distinct eigenvalues. -/
theorem eqw_two_eigenvalues [FiniteDimensional ℂ W₁] (f : Module.End ℂ W₁) (hs : f.IsSemisimple)
    (ht : LinearMap.trace ℂ W₁ f = 0) (hf : f ≠ 0) :
    ∃ μ ν : ℂ, μ ≠ ν ∧ f.HasEigenvalue μ ∧ f.HasEigenvalue ν := by
  obtain ⟨μ, hμ, hμ0⟩ : ∃ μ : ℂ, f.HasEigenvalue μ ∧ μ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf ((hs.eq_zero_iff_forall_eigenvalue).mpr h)
  by_contra hne
  push Not at hne
  have htop : f.eigenspace μ = ⊤ := by
    rw [← hs.iSup_eigenspace_eq_top]
    refine le_antisymm (le_iSup (fun ν => f.eigenspace ν) μ) (iSup_le fun ν => ?_)
    by_cases hν : ν = μ
    · rw [hν]
    · intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact Submodule.zero_mem _
      exact (hne μ ν (Ne.symm hν) hμ (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)).elim
  have hfμ : f = μ • (1 : Module.End ℂ W₁) := by
    ext x
    have hx : x ∈ f.eigenspace μ := htop ▸ Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.mp hx
  rw [hfμ, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  have hdim : Module.finrank ℂ W₁ = 0 := by
    have := (mul_eq_zero.mp ht).resolve_left hμ0
    exact_mod_cast this
  have := Module.finrank_zero_iff.mp hdim
  exact hf (Subsingleton.elim _ _)

/-- An operator squaring to `-1` has only the eigenvalues `±i`. -/
theorem eqw_eigenvalue_sq {W : Type*} [AddCommGroup W] [Module ℂ W] (F : Module.End ℂ W)
    (hF : F * F = -1) {a : ℂ} (ha : F.HasEigenvalue a) : a = Complex.I ∨ a = -Complex.I := by
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv.1
  have h : (a * a + 1) • v = 0 := by
    have := congrArg (fun G : Module.End ℂ W => G v) hF
    simp only [Module.End.mul_apply, hFv, map_smul, smul_smul, LinearMap.neg_apply,
      Module.End.one_apply] at this
    rw [add_smul, one_smul, this, neg_add_cancel]
  have h2 : (a - Complex.I) * (a + Complex.I) = 0 := by
    have := (smul_eq_zero.mp h).resolve_right hv.2
    linear_combination this + (Complex.I_sq) * 0 - Complex.I_sq
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl (sub_eq_zero.mp h3)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h3)

theorem spec_eqw_tensor_idle_aux [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂) (hs₁ : f₁.IsSemisimple)
    (hs₂ : f₂.IsSemisimple) (ht₁ : LinearMap.trace ℂ W₁ f₁ = 0)
    (ht₂ : LinearMap.trace ℂ W₂ f₂ = 0)
    (hsq : (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) *
      (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) = -1) :
    f₁ = 0 ∨ f₂ = 0 := by
  by_contra h
  push Not at h
  obtain ⟨μ₁, ν₁, h₁, hμ₁, hν₁⟩ := eqw_two_eigenvalues f₁ hs₁ ht₁ h.1
  obtain ⟨μ₂, ν₂, h₂, hμ₂, hν₂⟩ := eqw_two_eigenvalues f₂ hs₂ ht₂ h.2
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ :=
    spec_eqw_tensor_three_eigenvalues_aux f₁ f₂ hμ₁ hν₁ h₁ hμ₂ hν₂ h₂
  rcases eqw_eigenvalue_sq _ hsq ha with rfl | rfl <;>
    rcases eqw_eigenvalue_sq _ hsq hb with rfl | rfl <;>
    rcases eqw_eigenvalue_sq _ hsq hc with rfl | rfl <;>
    simp_all

end Tensor

section Assembly

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

theorem spec_eqw_hSU_of_centralizer_eq_aux
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y))
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ H pq, J.baseChange ℂ x ∈ H pq)
    (hiso₁₀ : ∀ x ∈ H (1, 0), ∀ y ∈ H (1, 0), E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ H (0, 1), ∀ y ∈ H (0, 1), E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) root) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) root))
    (hbalNeg : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-root)) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-root)))
    (hred : LieAlgebra.radical ℚ (hodgeLieAlgebra H hH) =
      LieAlgebra.center ℚ (hodgeLieAlgebra H hH))
    (hcomm : Subalgebra.centralizer ℚ (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) =
      Algebra.adjoin ℚ {J})
    (hclass : EQWClassification E hE J hJ hskew) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU E hE J hJ hskew).toSubmodule := by
  have hroot : root * root = -((3 : ℚ) : ℂ) := by
    rw [← sq, root_sq]; norm_num
  have hle : hodgeLieAlgebra H hH ≤ weilSU E J :=
    spec_eqw_hodgeLieAlgebra_le_weilSU_aux (by norm_num) root hroot E J hJ hsupp hJH hiso₁₀
      hiso₀₁ hbalPos hbalNeg
  exact hclass hAlt hdim (hodgeLieAlgebra H hH) (gradingOperator H hH) rfl
    (spec_eqw_gradingOperator_mul_self_aux hsupp) hle
    (spec_eqw_hasTrivialRadical_aux hdim (by norm_num) E hE J hJ hskew _ hle hcomm hred)
    hcomm (spec_eqw_not_hasPlusMinusIntertwiner_aux hdim (by norm_num) J hJ root hroot _ hcomm)

end Assembly

section Falsification

/-- The rational operator on `ℚ¹²` that copies block `3` (coordinates `6, 7`) onto block `0`
(coordinates `0, 1`) and is zero elsewhere. It commutes with `hsuJ`, which is the same on every
block, but not with `hsuCMTorus`, whose signs on blocks `0` and `3` differ.
Source: constructed here for the falsification check; `hsuJ₁₂`, `hsuCMTorus₁₂`. -/
def eqwShift₁₂ : Matrix (Fin 12) (Fin 12) ℚ := Matrix.of fun i j =>
  if i.val < 2 ∧ j.val = i.val + 6 then 1 else 0

example : eqwShift₁₂ 0 6 = 1 ∧ eqwShift₁₂ 1 7 = 1 ∧ eqwShift₁₂ 6 0 = 0 := by
  simp [eqwShift₁₂]

/-- The block shift commutes with `hsuJ`. -/
theorem eqwShift_comm_J : Matrix.toLin' eqwShift₁₂ * hsuJ = hsuJ * Matrix.toLin' eqwShift₁₂ := by
  apply LinearMap.ext; intro x; funext i
  fin_cases i <;>
    simp [hsuJ, hsuJ₁₂, eqwShift₁₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The block shift does not commute with `hsuCMTorus`. -/
theorem eqwShift_not_comm_T :
    Matrix.toLin' eqwShift₁₂ * hsuCMTorus ≠ hsuCMTorus * Matrix.toLin' eqwShift₁₂ := by
  intro h
  have := congrFun (congrArg (fun G : Module.End ℚ (Fin 12 → ℚ) => G (Pi.single 6 1)) h) 1
  simp [hsuCMTorus, hsuCMTorus₁₂, hsuJ₁₂, eqwShift₁₂, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at this
  norm_num at this

theorem spec_eqw_hsuCMHodge_centralizer_ne_aux :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal : Set (Module.End ℚ (Fin 12 → ℚ))) ≠
      Algebra.adjoin ℚ {hsuJ} := by
  intro h
  have hT : hsuCMTorus ∈ Subalgebra.centralizer ℚ
      (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal : Set (Module.End ℚ (Fin 12 → ℚ))) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    have hg' : g ∈ (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal).toSubmodule := hg
    rw [spec_hodgeLieAlgebra_hsuCMHodge, Submodule.mem_span_singleton] at hg'
    obtain ⟨r, rfl⟩ := hg'
    rw [smul_mul_assoc, mul_smul_comm]
  have hle : Algebra.adjoin ℚ {hsuJ} ≤
      Subalgebra.centralizer ℚ {Matrix.toLin' eqwShift₁₂} := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg, eqwShift_comm_J]
  have := hle (h ▸ hT)
  rw [Subalgebra.mem_centralizer_iff] at this
  exact eqwShift_not_comm_T (this _ rfl)

end Falsification

end HodgeLean.Foundations

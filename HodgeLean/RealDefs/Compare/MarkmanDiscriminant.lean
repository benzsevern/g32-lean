import HodgeLean.RealDefs.Compare.MarkmanTransport

/-!
# Markman's discriminant and the determinant class

The comparison uses the actual `eval2`, `herm`, and `DiscIs` definitions of the port.
`discIs_iff_model_detClass` proves the comparison for a positive `d` and nonzero rational `c`.
The polarization, its nondegeneracy, and its Rosati compatibility are extracted from the
ported package; no isometry or Gram-identification premise is assumed. Contraction intertwines
`fT` with the negative cohomology action. Reversing that action conjugates and negates the
Hermitian form, giving the factor `(-1)^(2m) = 1` in its rational determinant.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.RealDefs.Compare.Markman

set_option backward.isDefEq.respectTransparency false

open Module WeilClasses HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm

/-- In even quadratic-field dimension the negative action has the same determinant class.
Source: `negative_gramDet`, roadmap §1.2, step 4. -/
theorem weilDetClass_negative_of_even {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {a : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)]
    (E : LinearMap.BilinForm ℚ V)
    (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
    (hs : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hE : E.IsAlt) (hn : E.Nondegenerate)
    (heven : Even (finrank (QuadraticAlgebra ℚ a 0) (WithJ V J))) :
    weilDetClass E (negativeAction J) (negative_skew J E hs) hE hn =
      weilDetClass E J hs hE hn := by
  let b := Module.finBasis (QuadraticAlgebra ℚ a 0) (WithJ V J)
  unfold weilDetClass
  rw [detClass_eq _ _ (negativeBasis J b), detClass_eq _ _ b]
  congr 1
  apply Units.ext
  change gramDetℚ _ (negativeBasis J b) = gramDetℚ _ b
  rw [negative_gramDet J E hs hE b]
  obtain ⟨n, hn⟩ := heven
  simp only [Fintype.card_fin, hn, ← two_mul, pow_mul]
  norm_num

/-- Markman's contraction definition of the Riemann form agrees with ours on degree two.
Source: `eval2` and `Symplectic.contract`, evaluated on `u ∧ v`. -/
theorem eval2_eq_contract (n : ℕ) (ω : ⋀[ℚ]^2 (H1 ℚ n))
    (φ ψ : Module.Dual ℚ (H1 ℚ n)) :
    eval2 ℚ n ω φ ψ = ψ (contract ω φ) := by
  have hb : basisS ℚ n ∅ = 1 := by
    simp [basisS, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]
  have hc (q : ℚ) : (basisS ℚ n).repr (algebraMap ℚ (S ℚ n) q) ∅ = q := by
    rw [Algebra.algebraMap_eq_smul_one, ← hb]
    simp
  let L : (⋀[ℚ]^2 (H1 ℚ n)) →ₗ[ℚ] ℚ :=
    (basisS ℚ n).coord ∅ ∘ₗ D ℚ n ψ ∘ₗ D ℚ n φ ∘ₗ (⋀[ℚ]^2 (H1 ℚ n)).subtype
  have hL : L = ψ ∘ₗ (LinearMap.applyₗ φ :
      (Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] H1 ℚ n) →ₗ[ℚ] H1 ℚ n) ∘ₗ contract := by
    ext v
    simp [L, D, ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι, hc, Matrix.vecTail, mul_comm]
  exact LinearMap.congr_fun hL ω

private noncomputable def realDual (n : ℕ) (φ : Module.Dual ℚ (H1 ℚ n)) :
    Module.Dual ℝ (H1 ℝ n) :=
  ∑ i, (φ (e ℚ n i) : ℝ) • LinearMap.proj i

private theorem realDual_apply (n : ℕ) (φ : Module.Dual ℚ (H1 ℚ n)) (v : H1 ℚ n) :
    realDual n φ (bcH1 ℚ ℝ n v) = (φ v : ℝ) := by
  have hv : ∑ i, v i • e ℚ n i = v := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  have h := congrArg φ hv
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp only [realDual, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  change ∑ i, (φ (e ℚ n i) : ℝ) * (v i : ℝ) = (φ v : ℝ)
  rw [← h]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem eval2_bc_contract (n : ℕ) (ω : ⋀[ℚ]^2 (H1 ℚ n))
    (φ : Module.Dual ℚ (H1 ℚ n)) (ψ : Module.Dual ℝ (H1 ℝ n)) :
    eval2 ℝ n (bcS ℚ ℝ n ω) (realDual n φ) ψ =
      ψ (bcH1 ℚ ℝ n (contract ω φ)) := by
  have hb : basisS ℝ n ∅ = 1 := by
    simp [basisS, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]
  have hc (q : ℝ) : (basisS ℝ n).repr (algebraMap ℝ (S ℝ n) q) ∅ = q := by
    rw [Algebra.algebraMap_eq_smul_one, ← hb]
    simp
  let L : (⋀[ℚ]^2 (H1 ℚ n)) →ₗ[ℚ] ℝ :=
    ((basisS ℝ n).coord ∅).restrictScalars ℚ ∘ₗ (D ℝ n ψ).restrictScalars ℚ ∘ₗ
      (D ℝ n (realDual n φ)).restrictScalars ℚ ∘ₗ (bcS ℚ ℝ n).toLinearMap ∘ₗ
        (⋀[ℚ]^2 (H1 ℚ n)).subtype
  have hL : L = ψ.restrictScalars ℚ ∘ₗ bcH1 ℚ ℝ n ∘ₗ (LinearMap.applyₗ φ :
      (Module.Dual ℚ (H1 ℚ n) →ₗ[ℚ] H1 ℚ n) →ₗ[ℚ] H1 ℚ n) ∘ₗ contract := by
    ext v
    simp [L, D, bcS, ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι, hc, Matrix.vecTail, realDual_apply, mul_comm, Rat.smul_def]
  exact LinearMap.congr_fun hL ω

section Model

variable {m : ℕ} {A : AbVar (2 * m)} {d : ℚ} (X : PolarizedWeilType A d) (hd : 0 < d)

/-- Markman's action on cohomology, bundled with its quadratic relation.
Source: `WeilType.η` is a ring homomorphism and `(√−d)² = −d`. -/
noncomputable def modelAction :
    {J : H1 ℚ (2 * m) →ₗ[ℚ] H1 ℚ (2 * m) // J ∘ₗ J = -d • LinearMap.id} :=
  ⟨X.η (Kd.sqrtNeg d), by
    have hs : Kd.sqrtNeg d * Kd.sqrtNeg d = algebraMap ℚ (Kd d) (-d) := by
      apply Subtype.ext
      simpa [Kd.sqrtNeg, pow_two] using Port.sqrtNeg_sq hd.le
    have h := congrArg X.η hs
    rw [map_mul, RingHom.map_rat_algebraMap] at h
    simpa only [Algebra.algebraMap_eq_smul_one, Module.End.mul_eq_comp,
      Module.End.one_eq_id] using h⟩

example : (modelAction X hd).1.dualMap = X.fT := rfl

/-- The polarization in degree two, supplied by the Hodge-class part of ampleness.
Source: `PolarizedWeilType.ample` and `hodgeClassesX`. -/
noncomputable def modelPolarization : ⋀[ℚ]^2 (H1 ℚ (2 * m)) :=
  ⟨X.h, X.ample.1.1⟩

example : (modelPolarization X : S ℚ (2 * m)) = X.h := rfl

/-- Ampleness makes the rational polarization nondegenerate. A rational vector in its kernel
would extend to a real vector with zero value against its complex-structure transform,
contradicting the strict positivity in `IsAmple`.
Source: `PolarizedWeilType.ample`, via `eval2_bc_contract`. -/
theorem model_nondegenerate : IsNondegenerate (modelPolarization X) := by
  have hi : Function.Injective (contract (modelPolarization X)) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    by_contra hne
    have hr : realDual (2 * m) φ ≠ 0 := by
      intro hz
      apply hne
      apply LinearMap.ext
      intro v
      have h := realDual_apply (2 * m) φ v
      rw [hz, LinearMap.zero_apply] at h
      exact_mod_cast h.symm
    have hp := X.ample.2 (realDual (2 * m) φ) hr
    have he := eval2_bc_contract (2 * m) (modelPolarization X) φ
      (realDual (2 * m) φ ∘ₗ A.J)
    rw [hφ, map_zero, map_zero] at he
    exact (ne_of_gt hp) he
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq])).mp hi

/-- Markman's norm compatibility implies the Rosati condition on the actual polarization.
Source: `PolarizedWeilType.norm` at `√−d` and `map_eq_smul_iff_isRosatiSkew`. -/
theorem model_rosati : IsRosatiSkew (modelPolarization X) (modelAction X hd).1 := by
  apply (map_eq_smul_iff_isRosatiSkew hd.ne' (modelAction X hd).2 (modelPolarization X)).mp
  have hn : Kd.Nm d (Kd.sqrtNeg d) = d := by
    rw [Port.kdEquiv_norm d hd, Port.kdEquiv_sqrtNeg]
    simp [QuadraticAlgebra.norm_def]
  have hm : (⋀[ℚ]^2 (H1 ℚ (2 * m))).subtype ∘ₗ exteriorPower.map 2 (modelAction X hd).1 =
      (ExteriorAlgebra.map (modelAction X hd).1).toLinearMap ∘ₗ
        (⋀[ℚ]^2 (H1 ℚ (2 * m))).subtype := by
    ext v
    simp [Matrix.vecTail, Function.comp_def]
  apply Subtype.ext
  rw [show (exteriorPower.map 2 (modelAction X hd).1 (modelPolarization X) : S ℚ (2 * m)) =
      ExteriorAlgebra.map (modelAction X hd).1 X.h from LinearMap.congr_fun hm (modelPolarization X)]
  change ExteriorAlgebra.map (X.η (Kd.sqrtNeg d)) X.h = d • X.h
  rw [X.norm, hn]

theorem model_E_eq {ω : ⋀[ℚ]^2 (H1 ℚ (2 * m))} (hX : (ω : S ℚ (2 * m)) = X.h)
    (φ ψ : Module.Dual ℚ (H1 ℚ (2 * m))) : X.E φ ψ = riemannForm ω φ ψ := by
  rw [PolarizedWeilType.E, ← hX, eval2_eq_contract]
  rfl

/-- The actual complex-valued Hermitian form is the chosen embedding of our homology form.
Source: Markman's `herm`, `eval2_eq_contract`, and `kdEquiv_symm_coe`. -/
theorem model_herm_eq {ω : ⋀[ℚ]^2 (H1 ℚ (2 * m))} (hX : (ω : S ℚ (2 * m)) = X.h)
    (hR : IsRosatiSkew ω (modelAction X hd).1)
    (φ ψ : WithJ (Module.Dual ℚ (H1 ℚ (2 * m))) (transposeAction (modelAction X hd))) :
    X.herm (WithJ.equiv _ φ) (WithJ.equiv _ ψ) =
      ((Port.kdEquiv d hd).symm
        (weilHermitian (riemannForm ω) (transposeAction (modelAction X hd))
          (riemannForm_skew (modelAction X hd) hR) φ ψ) : ℂ) := by
  rw [Port.kdEquiv_symm_coe]
  simp only [re_weilHermitian, im_weilHermitian, PolarizedWeilType.herm,
    model_E_eq X hX]
  rfl

variable [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]

theorem model_homology_finrank :
    finrank (QuadraticAlgebra ℚ (-d) 0)
      (WithJ (Module.Dual ℚ (H1 ℚ (2 * m))) (transposeAction (modelAction X hd))) = 2 * m := by
  have h := finrank_withJ (transposeAction (modelAction X hd))
  rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun] at h
  omega

/-- Entrywise comparison of Markman's Gram matrix with the transported cohomology Gram matrix.
Source: `model_herm_eq` and `homologyEquiv_isometry`. -/
theorem model_gram {ω : ⋀[ℚ]^2 (H1 ℚ (2 * m))} (hX : (ω : S ℚ (2 * m)) = X.h)
    (hω : IsNondegenerate ω) (hR : IsRosatiSkew ω (modelAction X hd).1)
    (b : Basis (Fin (2 * m)) (QuadraticAlgebra ℚ (-d) 0)
      (WithJ (Module.Dual ℚ (H1 ℚ (2 * m))) (transposeAction (modelAction X hd)))) :
    (Matrix.of fun i j => X.herm (WithJ.equiv _ (b i)) (WithJ.equiv _ (b j))) =
      (LinearMap.toMatrix₂ (b.map (homologyEquiv (modelAction X hd) hω hR))
        (b.map (homologyEquiv (modelAction X hd) hω hR))
        (weilHermitian (dualForm hω) (negativeAction (modelAction X hd))
          (dualForm_negative_skew (modelAction X hd) hω hR))).map
        ((Kd d).subtype.comp (Port.kdEquiv d hd).symm.toRingHom) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.of_apply, Matrix.map_apply, LinearMap.toMatrix₂_apply,
    Basis.map_apply, homologyEquiv_isometry]
  exact model_herm_eq X hd hX hR (b i) (b j)

/-- The complex Gram determinant in `DiscIs` is exactly the rational Gram determinant of the
dual form with the negative cohomology action, in the transported basis.
Source: `model_herm_eq`, `homologyEquiv_gram`, and functoriality of the determinant. -/
theorem model_gramDet {ω : ⋀[ℚ]^2 (H1 ℚ (2 * m))} (hX : (ω : S ℚ (2 * m)) = X.h)
    (hω : IsNondegenerate ω) (hR : IsRosatiSkew ω (modelAction X hd).1)
    (b : Basis (Fin (2 * m)) (QuadraticAlgebra ℚ (-d) 0)
      (WithJ (Module.Dual ℚ (H1 ℚ (2 * m))) (transposeAction (modelAction X hd)))) :
    (Matrix.of fun i j => X.herm (WithJ.equiv _ (b i)) (WithJ.equiv _ (b j))).det =
      (gramDetℚ (weilHermitian (dualForm hω) (negativeAction (modelAction X hd))
          (dualForm_negative_skew (modelAction X hd) hω hR))
        (b.map (homologyEquiv (modelAction X hd) hω hR)) : ℂ) := by
  let f : QuadraticAlgebra ℚ (-d) 0 →+* ℂ :=
    (Kd d).subtype.comp (Port.kdEquiv d hd).symm.toRingHom
  let H := weilHermitian (dualForm hω) (negativeAction (modelAction X hd))
    (dualForm_negative_skew (modelAction X hd) hω hR)
  let e := b.map (homologyEquiv (modelAction X hd) hω hR)
  have hm : (Matrix.of fun i j => X.herm (WithJ.equiv _ (b i)) (WithJ.equiv _ (b j))) =
      (LinearMap.toMatrix₂ e e H).map f := model_gram X hd hX hω hR b
  rw [hm]
  have hf : f (gramDet H e) = ((LinearMap.toMatrix₂ e e H).map f).det := f.map_det _
  rw [← hf, ← algebraMap_gramDetℚ (isSymm_weilHermitian (isAlt_dualForm hω))]
  simp [f, e]

/-- The actual `DiscIs` predicate equals the determinant-class predicate for the transported
dual form. The cohomology generator is negative because contraction is Rosati-skew.
Source: roadmap §1.2, steps 1–4, `model_gramDet` and the quotient by the norm subgroup. -/
theorem discIs_iff_negative_detClass {ω : ⋀[ℚ]^2 (H1 ℚ (2 * m))}
    (hX : (ω : S ℚ (2 * m)) = X.h) (hω : IsNondegenerate ω)
    (hR : IsRosatiSkew ω (modelAction X hd).1) {c : ℚ} (hc : c ≠ 0) :
    X.DiscIs c ↔
      weilDetClass (dualForm hω) (negativeAction (modelAction X hd))
        (dualForm_negative_skew (modelAction X hd) hω hR)
        (isAlt_dualForm hω) (nondegenerate_dualForm hω) =
      ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-d) 0)) := by
  let J := modelAction X hd
  let T := transposeAction J
  let H := weilHermitian (dualForm hω) (negativeAction J) (dualForm_negative_skew J hω hR)
  have hH : H.IsSymm := isSymm_weilHermitian (isAlt_dualForm hω)
  have hN : H.Nondegenerate := nondegenerate_weilHermitian (nondegenerate_dualForm hω)
  change X.DiscIs c ↔ detClass H hH hN = _
  constructor
  · rintro ⟨b, hb, k, hk, hdet⟩
    have hbK : LinearIndependent (QuadraticAlgebra ℚ (-d) 0)
        (fun i => (WithJ.equiv T).symm (b i)) :=
      (linearIndependent_double_iff T b).mp hb
    let bk := basisOfLinearIndependentOfCardEqFinrank' _ hbK (by
      simpa using (model_homology_finrank X hd).symm)
    let e := bk.map (homologyEquiv J hω hR)
    apply (detClass_eq_iff_exists_norm hH hN hc (Fin (2 * m)) e).mpr
    refine ⟨Port.kdEquiv d hd k, (map_ne_zero (Port.kdEquiv d hd)).mpr hk, ?_⟩
    have hg := model_gramDet X hd hX hω hR bk
    change (Matrix.of fun i j => X.herm (WithJ.equiv T (bk i)) (WithJ.equiv T (bk j))).det =
      (gramDetℚ H e : ℂ) at hg
    have hbk : ∀ i, WithJ.equiv T (bk i) = b i := by intro i; simp [bk]
    simp only [hbk] at hg
    have heq : (gramDetℚ H e : ℂ) = (c : ℂ) * ((QuadraticAlgebra.norm (Port.kdEquiv d hd k) : ℚ) : ℂ) := by
      rw [← Port.kdEquiv_norm d hd k]
      exact hg.symm.trans hdet
    exact_mod_cast heq
  · intro hclass
    let b := (Module.finBasis (QuadraticAlgebra ℚ (-d) 0)
      (WithJ (Module.Dual ℚ (H1 ℚ (2 * m))) T)).reindex
        (finCongr (model_homology_finrank X hd))
    let e := b.map (homologyEquiv J hω hR)
    obtain ⟨z, hz, hdet⟩ := (detClass_eq_iff_exists_norm hH hN hc (Fin (2 * m)) e).mp hclass
    refine ⟨fun i => WithJ.equiv T (b i), ?_, (Port.kdEquiv d hd).symm z, ?_, ?_⟩
    · apply (linearIndependent_double_iff T _).mpr
      simpa using b.linearIndependent
    · exact (map_ne_zero (Port.kdEquiv d hd).symm).mpr hz
    · rw [model_gramDet X hd hX hω hR b]
      change (gramDetℚ H e : ℂ) = _
      rw [hdet, Port.kdEquiv_norm d hd, AlgEquiv.apply_symm_apply]
      push_cast
      rfl

/-- **Discriminant comparison on `H¹`.** For a positive `d`, a nondegenerate polarization
2-vector identified with Markman's `h`, and its Rosati action, `DiscIs c` holds exactly when
the dual-form determinant class is `[c]`. No sign correction survives: the dimension is `2m`.
Source: roadmap §1.2; the concrete contraction isometry and `negative_gramDet` proved here. -/
theorem discIs_iff_detClass {ω : ⋀[ℚ]^2 (H1 ℚ (2 * m))}
    (hX : (ω : S ℚ (2 * m)) = X.h) (hω : IsNondegenerate ω)
    (hR : IsRosatiSkew ω (modelAction X hd).1) {c : ℚ} (hc : c ≠ 0) :
    X.DiscIs c ↔
      weilDetClass (dualForm hω) (modelAction X hd)
        ((isRosatiSkew_iff_dualForm hω _).mp hR)
        (isAlt_dualForm hω) (nondegenerate_dualForm hω) =
      ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-d) 0)) := by
  rw [discIs_iff_negative_detClass X hd hX hω hR hc]
  rw [weilDetClass_negative_of_even (dualForm hω) (modelAction X hd)
    ((isRosatiSkew_iff_dualForm hω _).mp hR) (isAlt_dualForm hω) (nondegenerate_dualForm hω)]
  have h := finrank_withJ (modelAction X hd)
  rw [Module.finrank_fin_fun] at h
  have he : finrank (QuadraticAlgebra ℚ (-d) 0) (WithJ (H1 ℚ (2 * m)) (modelAction X hd)) =
      2 * m := by omega
  rw [he]
  exact even_two_mul m

/-- The canonical comparison, with the polarization, nondegeneracy and Rosati compatibility
obtained directly from Markman's package.
Source: `discIs_iff_detClass`, `model_nondegenerate`, and `model_rosati`. -/
theorem discIs_iff_model_detClass
    {c : ℚ} (hc : c ≠ 0) :
    X.DiscIs c ↔
      weilDetClass (dualForm (model_nondegenerate X)) (modelAction X hd)
        ((isRosatiSkew_iff_dualForm (model_nondegenerate X) _).mp (model_rosati X hd))
        (isAlt_dualForm (model_nondegenerate X)) (nondegenerate_dualForm (model_nondegenerate X)) =
      ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-d) 0)) :=
  discIs_iff_detClass X hd rfl (model_nondegenerate X) (model_rosati X hd) hc

end Model

/-- The `d = 3`, dimension-six comparison is an instance of the general theorem.
Source: `discIs_iff_model_detClass`, specialized to the F-1569 discriminant. -/
example {A : AbVar (2 * 3)} (X : PolarizedWeilType A 3) :
    X.DiscIs (-2) ↔
      weilDetClass (dualForm (model_nondegenerate X)) (modelAction X (by norm_num))
        ((isRosatiSkew_iff_dualForm (model_nondegenerate X) _).mp (model_rosati X (by norm_num)))
        (isAlt_dualForm (model_nondegenerate X)) (nondegenerate_dualForm (model_nondegenerate X)) =
      classNegTwo :=
  discIs_iff_model_detClass X (by norm_num) (by norm_num)

end HodgeLean.RealDefs.Compare.Markman

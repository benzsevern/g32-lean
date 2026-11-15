module

public import HodgeLean.Foundations.Program.GaussManinToriLatticeDefs

/-! # Period matrices, their lattices and `H^{1,0}`: proof obligations (Mathlib only) -/

@[expose] public noncomputable section

open scoped TensorProduct Matrix

namespace HodgeLean.Foundations.Program

section Witnesses

/-- The real map of `(1, τ)`: `s ↦ s₀ + s₁ τ`. -/
theorem d2l_ellipticRealMap (τ : ℂ) (s : Fin (2 * 1) → ℝ) :
    d2_realMap (d2_ellipticPeriod τ) s = fun _ ↦ (s 0 : ℂ) + s 1 * τ := by
  funext i
  rw [d2_realMap, Fintype.linearCombination_apply, Finset.sum_apply]
  simp [Fin.sum_univ_two, d2_column, d2_ellipticPeriod, Complex.real_smul]

/-- The standard form in coordinates: `E(s, t) = s₀ t₁ - s₁ t₀`. -/
theorem d2l_stdRiemann_real (s t : Fin (2 * 1) → ℝ) :
    d2_riemannReal d2_stdRiemann s t = s 0 * t 1 - s 1 * t 0 := by
  simp [d2_riemannReal, d2_stdRiemann, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Real and imaginary parts of `P s' = i P s` for `(1, τ)`. -/
theorem d2l_elliptic_rel {τ : ℂ} {s s' : Fin (2 * 1) → ℝ}
    (h : d2_realMap (d2_ellipticPeriod τ) s' = Complex.I • d2_realMap (d2_ellipticPeriod τ) s) :
    s' 0 + s' 1 * τ.re = -(s 1 * τ.im) ∧ s' 1 * τ.im = s 0 + s 1 * τ.re := by
  rw [d2l_ellipticRealMap, d2l_ellipticRealMap] at h
  have h0 := congrFun h 0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp at hre him
  constructor <;> linarith

theorem d2_ellipticPeriod_isPeriodMatrix_aux {τ : ℂ} (hτ : τ.im ≠ 0) :
    d2_IsPeriodMatrix (d2_ellipticPeriod τ) := by
  rw [d2_IsPeriodMatrix, linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  have h := congrFun (show d2_realMap (d2_ellipticPeriod τ) s = 0 from hs) 0
  rw [d2l_ellipticRealMap] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  have h1 : s 1 = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hτ
  have h0 : s 0 = 0 := by rw [h1] at hre; simpa using hre
  funext k
  fin_cases k
  · exact h0
  · exact h1

theorem d2_ellipticPeriod_isRiemannForm_aux {τ : ℂ} (hτ : 0 < τ.im) :
    d2_IsRiemannForm (d2_ellipticPeriod τ) d2_stdRiemann := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · intro s t s' t' hs ht
    obtain ⟨hs1, hs2⟩ := d2l_elliptic_rel hs
    obtain ⟨ht1, ht2⟩ := d2l_elliptic_rel ht
    rw [d2l_stdRiemann_real, d2l_stdRiemann_real]
    linear_combination t' 1 * hs1 - s' 1 * ht1 + t 1 * hs2 - s 1 * ht2
  · intro s s' hs hrel
    obtain ⟨h1, h2⟩ := d2l_elliptic_rel hrel
    rw [d2l_stdRiemann_real]
    have key : (s 0 * s' 1 - s 1 * s' 0) * τ.im = (s 0 + s 1 * τ.re) ^ 2 + (s 1 * τ.im) ^ 2 := by
      linear_combination (s 0 + s 1 * τ.re) * h2 - s 1 * τ.im * h1
    by_contra hE
    replace hE := not_lt.1 hE
    have hle : (s 0 + s 1 * τ.re) ^ 2 + (s 1 * τ.im) ^ 2 ≤ 0 := by
      rw [← key]; exact mul_nonpos_of_nonpos_of_nonneg hE hτ.le
    have ha : s 0 + s 1 * τ.re = 0 := by
      nlinarith [sq_nonneg (s 0 + s 1 * τ.re), sq_nonneg (s 1 * τ.im)]
    have hb : s 1 * τ.im = 0 := by
      nlinarith [sq_nonneg (s 0 + s 1 * τ.re), sq_nonneg (s 1 * τ.im)]
    have hs1 : s 1 = 0 := (mul_eq_zero.1 hb).resolve_right hτ.ne'
    have hs0 : s 0 = 0 := by rw [hs1] at ha; simpa using ha
    apply hs
    funext k
    fin_cases k
    · exact hs0
    · exact hs1

theorem d2_ellipticPeriod_not_isRiemannForm_aux {τ : ℂ} (hτ : τ.im < 0) :
    ¬ d2_IsRiemannForm (d2_ellipticPeriod τ) d2_stdRiemann := by
  intro hA
  have hy := hτ.ne
  let s : Fin (2 * 1) → ℝ := fun k ↦ if (k : ℕ) = 0 then 1 else 0
  let s' : Fin (2 * 1) → ℝ := fun k ↦ if (k : ℕ) = 0 then -τ.re / τ.im else 1 / τ.im
  have hs : s ≠ 0 := fun h ↦ by simpa [s] using congrFun h 0
  have hrel : d2_realMap (d2_ellipticPeriod τ) s' =
      Complex.I • d2_realMap (d2_ellipticPeriod τ) s := by
    rw [d2l_ellipticRealMap, d2l_ellipticRealMap]
    funext i
    apply Complex.ext
    · simp [s, s']; field_simp; ring
    · simp [s, s']; field_simp
  have h := hA.positive s s' hs hrel
  rw [d2l_stdRiemann_real] at h
  simp [s, s'] at h
  linarith [one_div_neg.2 hτ]

end Witnesses

section Lattice

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

theorem d2l_card_eq_finrank : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
  rw [Fintype.card_fin, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- The columns of a period matrix as an `ℝ`-basis of `ℂ^g`: `2g` independent vectors in a space
of real dimension `2g`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1;
`basisOfLinearIndependentOfCardEqFinrank'`. -/
def d2l_basis (hP : d2_IsPeriodMatrix P) : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ hP d2l_card_eq_finrank

theorem d2l_basis_coe (hP : d2_IsPeriodMatrix P) : ⇑(d2l_basis hP) = d2_column P :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ hP d2l_card_eq_finrank

example (hP : d2_IsPeriodMatrix P) (k : Fin (2 * g)) : d2l_basis hP k = d2_column P k := by
  rw [d2l_basis_coe]

theorem d2l_lattice_eq (hP : d2_IsPeriodMatrix P) :
    d2_lattice P = Submodule.span ℤ (Set.range (d2l_basis hP)) := by
  rw [d2l_basis_coe]; rfl

theorem d2_lattice_discrete_aux (hP : d2_IsPeriodMatrix P) :
    DiscreteTopology (d2_lattice P) := by
  rw [d2l_lattice_eq hP]; infer_instance

theorem d2_lattice_isZLattice_aux (hP : d2_IsPeriodMatrix P) :
    haveI := d2_lattice_discrete_aux hP
    IsZLattice ℝ (d2_lattice P) := by
  have := d2_lattice_discrete_aux hP
  exact ⟨by rw [d2l_lattice_eq hP]; exact ZSpan.span_top _⟩

theorem d2_markingMap_injective_aux (hP : d2_IsPeriodMatrix P) :
    Function.Injective (d2_markingMap P) :=
  (linearIndependent_iff_injective_fintypeLinearCombination).1 (hP.restrict_scalars' ℤ)

theorem d2_isPeriodMatrix_of_isRiemannForm_aux {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
    (hA : d2_IsRiemannForm P A) : d2_IsPeriodMatrix P := by
  rw [d2_IsPeriodMatrix, linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro s hs
  by_contra hne
  have h := hA.positive s 0 hne (by
    rw [map_zero, show d2_realMap P s = 0 from hs, smul_zero])
  simp [d2_riemannReal] at h

theorem d2_finrank_hodgeOne_aux (hP : d2_IsPeriodMatrix P) :
    Module.finrank ℂ (d2_hodgeOne P) = g := by
  have hinj : Function.Injective (d2_evalBilin P : Module.Dual ℂ (Fin g → ℂ) →ₗ[ℂ] _) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    have hcol : ∀ k, φ (d2_column P k) = 0 := fun k ↦ by
      have := congrFun ((d2_vec (2 * g)).map_eq_zero_iff.1 hφ) k
      exact this
    have : φ.restrictScalars ℝ = 0 :=
      (d2l_basis hP).ext fun k ↦ by rw [d2l_basis_coe]; exact hcol k
    exact LinearMap.ext fun v ↦ LinearMap.congr_fun this v
  rw [d2_hodgeOne, LinearMap.finrank_range_of_inj hinj, Subspace.dual_finrank_eq,
    Module.finrank_fin_fun]

end Lattice

end HodgeLean.Foundations.Program

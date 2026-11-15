import HodgeLean.Adapters.ThetaExistence
import HodgeLean.Adapters.AutomorphyLineBundleOnX
import HodgeLean.Adapters.UniformizationBiholomorphic
import HodgeLean.Foundations.AnalyticDivisorAlgebraic
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2
import HodgeLean.Foundations.AnalyticDivisorAlgebraic3

/-! # Proof obligations for the theta-divisor-on-`X(ℂ)` specification -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

set_option linter.unusedSectionVars false in
theorem spec_twist_eq_self_of_integral_aux (D : Datum (V := V)) (w : V)
    (hw : ∀ l : D.lattice, ∃ n : ℤ, D.hermitian.imaginary l w = n) :
    D.twist w = D := by
  have hs : (fun l ↦ D.semicharacter l * Circle.exp (2 * Real.pi * D.hermitian.imaginary l w)) =
      D.semicharacter := by
    funext l
    obtain ⟨n, hn⟩ := hw l
    rw [hn, Circle.exp_two_pi_mul_int, mul_one]
  unfold Datum.twist
  cases D
  simp only at hs
  simp only [hs]

set_option linter.unusedVariables false in
theorem spec_exists_zero_of_isPositiveDefinite_aux [Nontrivial V] (D : Datum (V := V))
    (hH : D.hermitian.IsPositiveDefinite) (θ : V → ℂ) (hθ : θ ∈ sections D) (hne : θ ≠ 0) :
    ∃ v : V, θ v = 0 := by
  by_contra hz
  push Not at hz
  obtain ⟨hd, hfe⟩ := hθ
  set H := D.hermitian with hHdef
  have hHc : Continuous fun x : V ↦ (H.toFun x x).re :=
    Complex.continuous_re.comp ((hermitianCLM H).continuous₂.comp
      (continuous_id.prodMk continuous_id))
  let ρ : V → ℝ := fun v ↦ ‖θ v‖⁻¹ * Real.exp (Real.pi / 2 * (H.toFun v v).re)
  have hρc : Continuous ρ := ((hd.continuous.norm).inv₀ fun v ↦ norm_ne_zero_iff.2 (hz v)).mul
    (Real.continuous_exp.comp (continuous_const.mul hHc))
  have hre : ∀ l v : V, (H.toFun v l).re = (H.toFun l v).re := fun l v ↦ by
    rw [← H.conj_symm v l]
    exact Complex.conj_re _
  have hfn : ∀ (l : D.lattice) v, ‖holFactor D l v‖ =
      Real.exp (Real.pi * (H.toFun l v).re + Real.pi / 2 * (H.toFun l l).re) := by
    intro l v
    rw [holFactor, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp]
    congr 1
    simp [hHdef]
  have hper : ∀ (l : D.lattice) v, ρ (v + l) = ρ v := by
    intro l v
    simp only [ρ]
    rw [hfe l v, norm_mul, hfn, mul_inv, H.add_left, H.add_right, H.add_right]
    simp only [Complex.add_re]
    rw [hre l v, ← Real.exp_neg, mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have : Module.Free ℤ D.lattice := ZLattice.module_free ℝ D.lattice
  have : Module.Finite ℤ D.lattice := ZLattice.module_finite ℝ D.lattice
  let b := (Module.Free.chooseBasis ℤ D.lattice).ofZLatticeBasis ℝ D.lattice
  have hspan : Submodule.span ℤ (Set.range b) = D.lattice :=
    Module.Basis.ofZLatticeBasis_span ℝ D.lattice _
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hρc.continuousOn
  have hall : ∀ v, ρ v = ρ (ZSpan.fract b v) := by
    intro v
    have hm : (ZSpan.floor b v : V) ∈ D.lattice := hspan.le (ZSpan.floor b v).2
    rw [ZSpan.fract_apply]
    conv_lhs => rw [← sub_add_cancel v (ZSpan.floor b v : V)]
    exact hper ⟨_, hm⟩ _
  have hρb : ∀ v, ρ v ≤ C := fun v ↦ by
    rw [hall]
    exact (Real.le_norm_self _).trans
      (hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b v)))
  have hnn : ∀ v, 0 ≤ (H.toFun v v).re := fun v ↦ by
    by_cases hv : v = 0
    · simp [hv, hermitian_zero_left]
    · exact (hH v hv).le
  have hfb : ∀ v, ‖(θ v)⁻¹‖ * Real.exp (Real.pi / 2 * (H.toFun v v).re) ≤ C := fun v ↦ by
    rw [norm_inv]; exact hρb v
  have hbd : Bornology.IsBounded (Set.range fun v ↦ (θ v)⁻¹) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨v, rfl⟩
    refine le_trans ?_ (hfb v)
    exact le_mul_of_one_le_right (norm_nonneg _)
      (Real.one_le_exp (mul_nonneg (by positivity) (hnn v)))
  have hc : ∀ v, (θ v)⁻¹ = (θ 0)⁻¹ := fun v ↦
    (hd.inv hz).apply_eq_apply_of_bounded hbd v 0
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have ha : 0 < (H.toFun u u).re := hH u hu
  have hc0 : 0 < ‖(θ 0)⁻¹‖ := norm_pos_iff.2 (inv_ne_zero (hz 0))
  have hC0 : 0 ≤ C := le_trans (by positivity) (hfb 0)
  have hs : 0 < Real.pi / 2 * (H.toFun u u).re := by positivity
  set x := C / ‖(θ 0)⁻¹‖ / (Real.pi / 2 * (H.toFun u u).re) with hx
  have hx0 : 0 ≤ x := by positivity
  have hhom : (H.toFun (Real.sqrt x • u) (Real.sqrt x • u)).re = x * (H.toFun u u).re := by
    rw [hermitian_real_smul_left, hermitian_real_smul_right, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, Real.mul_self_sqrt hx0]
  have h1 := hfb (Real.sqrt x • u)
  rw [hc, hhom] at h1
  have h2 : Real.pi / 2 * (x * (H.toFun u u).re) = C / ‖(θ 0)⁻¹‖ := by
    rw [hx]; field_simp
  rw [h2] at h1
  have h3 := Real.add_one_le_exp (C / ‖(θ 0)⁻¹‖)
  have h4 : ‖(θ 0)⁻¹‖ * (C / ‖(θ 0)⁻¹‖ + 1) = C + ‖(θ 0)⁻¹‖ := by
    rw [mul_add, mul_div_cancel₀ _ hc0.ne', mul_one]
  nlinarith [mul_le_mul_of_nonneg_left h3 hc0.le]

end General

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem spec_isClosedAnalytic_abelianExp_image_aux (S : Set (Fin (dim X.left) → ℂ))
    (hS : IsClosedAnalytic (Fin (dim X.left) → ℂ) S)
    (hinv : ∀ v ∈ S, ∀ l : abelianPeriodLattice X, v + l ∈ S) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ) (abelianExp X '' S) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have := spec_lieGroup_complexPoint X (dim X.left)
  have hpre : abelianExp X ⁻¹' (abelianExp X '' S) = S := by
    ext v
    refine ⟨fun ⟨w, hw, hwv⟩ ↦ ?_, fun hv ↦ ⟨v, hv, rfl⟩⟩
    simpa using hinv w hw ⟨v - w, sub_mem_of_abelianExp_eq X hwv⟩
  have hc : (abelianExp X '' S)ᶜ = abelianExp X '' Sᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := surjective_abelianExp X x
      exact ⟨v, fun hv ↦ hx ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩ hx
      have hmem : v ∈ abelianExp X ⁻¹' (abelianExp X '' S) := hx
      rw [hpre] at hmem
      exact hv hmem
  have hcl : IsClosed (abelianExp X '' S) := by
    rw [← isOpen_compl_iff, hc]
    exact isOpenMap_abelianExp X _ hS.isClosed.isOpen_compl
  refine AnalyticDivisorAlgebraic3.spec_isClosedAnalytic_of_localBiholomorph (π := abelianExp X)
    hcl ?_ (by rwa [hpre])
  rintro x -
  obtain ⟨v, rfl⟩ := surjective_abelianExp X x
  obtain ⟨e, hve, heq, hs⟩ := spec_complexExponential_localBiholomorph X (dim X.left) v
  have hexp : abelianExp X v = e v := heq hve
  exact ⟨e, by rw [hexp]; exact e.map_source hve, heq, hs⟩

theorem spec_isClosedAnalytic_thetaZeroLocusX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ) (thetaZeroLocusX X θ) := by
  refine spec_isClosedAnalytic_abelianExp_image_aux X {v | θ v = 0}
    (AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_theta _ hθ) fun v hv l ↦ ?_
  exact (AnalyticDivisorAlgebraic.spec_theta_add_eq_zero_iff _ hθ l v).2 hv

theorem spec_thetaZeroLocusX_nonempty_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) (hg : 0 < dim X.left)
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) :
    (thetaZeroLocusX X θ).Nonempty := by
  have : Nonempty (Fin (dim X.left)) := ⟨⟨0, hg⟩⟩
  obtain ⟨v, hv⟩ := spec_exists_zero_of_isPositiveDefinite_aux (datumOfX X H E hE χ hχ) hH θ hθ hne
  exact ⟨abelianExp X v, v, hv, rfl⟩

theorem spec_thetaZeroLocusX_hypersurface_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hH : H.IsPositiveDefinite) (hg : 0 < dim X.left) :
    (∃ θ ∈ sections (datumOfX X H E hE χ hχ), θ ≠ 0) ∧
      ∀ θ ∈ sections (datumOfX X H E hE χ hχ), θ ≠ 0 →
        IsClosedAnalytic (Fin (dim X.left) → ℂ) (thetaZeroLocusX X θ) ∧
          (thetaZeroLocusX X θ).Nonempty ∧ interior (thetaZeroLocusX X θ) = ∅ := by
  refine ⟨Submodule.exists_mem_ne_zero_of_ne_bot (spec_sections_ne_bot _ hH),
    fun θ hθ hne ↦ ⟨spec_isClosedAnalytic_thetaZeroLocusX_aux X H E hE χ hχ θ hθ,
      spec_thetaZeroLocusX_nonempty_aux X H E hE χ hχ hH hg θ hθ hne,
      spec_interior_thetaZeroLocusX X H E hE χ hχ θ hθ hne⟩⟩

theorem abelianExp_add_eq_mul (v w : Fin (dim X.left) → ℂ) :
    abelianExp X (v + w) = abelianExp X v * abelianExp X w := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  change (complexExponentialHom X (dim X.left) (v + w)).toMul =
    (complexExponentialHom X (dim X.left) v).toMul * (complexExponentialHom X (dim X.left) w).toMul
  rw [map_add]
  rfl

theorem spec_thetaZeroLocusX_translate_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (w : Fin (dim X.left) → ℂ) :
    thetaZeroLocusX X (fun v ↦ Complex.exp (-(Real.pi * H.toFun w v)) * θ (v + w)) =
      (fun x ↦ x * abelianExp X w) ⁻¹' thetaZeroLocusX X θ := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : Complex.exp (-(Real.pi * H.toFun w v)) * θ (v + w) = 0 := hv
    exact ⟨v + w, (mul_eq_zero.1 hv').resolve_left (Complex.exp_ne_zero _),
      abelianExp_add_eq_mul X v w⟩
  · rintro ⟨u, hu, hux⟩
    have hu' : θ u = 0 := hu
    refine ⟨u - w, ?_, ?_⟩
    · change Complex.exp (-(Real.pi * H.toFun w (u - w))) * θ (u - w + w) = 0
      rw [sub_add_cancel, hu', mul_zero]
    · apply mul_right_cancel (b := abelianExp X w)
      rw [← abelianExp_add_eq_mul, sub_add_cancel, hux]

theorem spec_thetaZeroLocusX_translate_of_integral_aux
    (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ))
    (hne : θ ≠ 0) (w : Fin (dim X.left) → ℂ)
    (hw : ∀ l : abelianPeriodLattice X, ∃ n : ℤ, H.imaginary l w = n) :
    ∃ θ' ∈ sections (datumOfX X H E hE χ hχ), θ' ≠ 0 ∧
      thetaZeroLocusX X θ' = (fun x ↦ x * abelianExp X w) ⁻¹' thetaZeroLocusX X θ := by
  set D := datumOfX X H E hE χ hχ
  have hD : D.twist w = D := spec_twist_eq_self_of_integral_aux D w hw
  refine ⟨fun v ↦ Complex.exp (-(Real.pi * H.toFun w v)) * θ (v + w), ?_, ?_,
    spec_thetaZeroLocusX_translate_aux X H θ w⟩
  · have h := spec_sections_translate D w θ hθ
    rw [hD] at h
    exact h
  · intro h
    apply hne
    funext v
    have := congrFun h (v - w)
    simpa only [sub_add_cancel, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero,
      false_or] using this

theorem spec_isClosedAnalytic_singularLocusX_aux
    (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : θ ∈ sections (datumOfX X H E hE χ hχ)) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      (abelianExp X '' {v | θ v = 0 ∧ fderiv ℂ θ v = 0}) := by
  set D := datumOfX X H E hE χ hχ
  refine spec_isClosedAnalytic_abelianExp_image_aux X _
    (AnalyticDivisorAlgebraic3.spec_isClosedAnalytic_singularLocus hθ.1) ?_
  rintro v ⟨hv, hdv⟩ l
  exact ⟨(AnalyticDivisorAlgebraic.spec_theta_add_eq_zero_iff D hθ l v).2 hv,
    (AnalyticDivisorAlgebraic3.spec_fderiv_theta_add_eq_zero_iff D hθ l hv).2 hdv⟩

theorem spec_thetaZeroLocusX_eq_univ_of_hermitian_zero_aux
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m *
        Circle.exp (Real.pi * (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m))
    (h0 : ∀ l m : abelianPeriodLattice X,
      ((0 : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) l m : ℝ) =
        (HermitianForm.zero (V := Fin (dim X.left) → ℂ)).imaginary l m)
    (hne : ∃ l, χ l ≠ 1) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X HermitianForm.zero 0 h0 χ hχ)) :
    thetaZeroLocusX X θ = Set.univ := by
  have hbot := spec_sections_eq_bot_of_hermitian_zero
    (datumOfX X HermitianForm.zero 0 h0 χ hχ) (fun _ _ ↦ rfl) hne
  rw [hbot] at hθ
  have h0θ : θ = 0 := hθ
  subst h0θ
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨v, rfl⟩ := surjective_abelianExp X x
  exact ⟨v, rfl, rfl⟩

theorem spec_thetaZeroLocusX_trivial_eq_empty_aux :
    (fun _ ↦ (1 : ℂ)) ∈ sections (datumOfXTrivial X) ∧
      thetaZeroLocusX X (fun _ ↦ (1 : ℂ)) = ∅ := by
  refine ⟨⟨differentiable_const 1, fun l v ↦ ?_⟩, ?_⟩
  · simp [holFactor, datumOfXTrivial, datumOfX, HermitianForm.zero]
  · simp [thetaZeroLocusX]

end HodgeLean.Adapters

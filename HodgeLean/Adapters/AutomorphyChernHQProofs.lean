import HodgeLean.Adapters.AutomorphyChernHQDefs
import HodgeLean.Adapters.LatticeClassHQ
import HodgeLean.Foundations.AutomorphyChernClass

/-! # Proofs for the Chern form in `HQ X 2` on `X`'s own period lattice

The statements are frozen; this file proves them. All seven are proved, by two parallel provers.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass

namespace HodgeLean.Adapters

section Sign

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- `L_{-η}^r = (-1)^r L_η^r`. -/
theorem lefschetzPow_neg_aux (μ : CupProduct X) (η : HQ X 2) :
    ∀ (r : ℕ) {k m : ℕ} (h : k + 2 * r = m),
      lefschetzPow X μ (-η) r h = ((-1 : ℚ) ^ r) • lefschetzPow X μ η r h
  | 0, _, _, rfl => by simp [lefschetzPow]
  | r + 1, k, _, rfl => by
    simp only [lefschetzPow]
    rw [lefschetzPow_neg_aux μ η r rfl]
    ext a
    simp [pow_succ]

/-- Hard Lefschetz for `η` gives it for `-η`. -/
theorem hardLefschetz_neg_of_aux (μ : CupProduct X) (η : HQ X 2) (h : HardLefschetz X μ η) :
    HardLefschetz X μ (-η) := by
  refine ⟨fun hk hm => ?_⟩
  rw [lefschetzPow_neg_aux]
  rcases neg_one_pow_eq_or ℚ (dim X.left - _) with h1 | h1 <;> rw [h1]
  · rw [one_smul]; exact h.bijective hk hm
  · rw [neg_one_smul]; exact (Equiv.neg _).bijective.comp (h.bijective hk hm)

theorem spec_hardLefschetz_neg_iff_aux (μ : CupProduct X) (η : HQ X 2) :
    HardLefschetz X μ (-η) ↔ HardLefschetz X μ η :=
  ⟨fun h => neg_neg η ▸ hardLefschetz_neg_of_aux X μ (-η) h, hardLefschetz_neg_of_aux X μ η⟩

end Sign

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem spec_datumOfX_imForm_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)) :
    (datumOfX X H E hE χ hχ).imForm = E := by
  refine AddMonoidHom.ext fun l => AddMonoidHom.ext fun m => ?_
  exact (congrArg Int.floor (hE l m).symm).trans (Int.floor_intCast _)

/-- An alternating integral form on a free finite `ℤ`-module has a semicharacter:
`χ(l) = exp(π F(l, l))` with `F` the strictly upper triangular part of `E` in a basis, so that
`F - Fᵀ = E`. -/
theorem exists_semicharacter_of_alternating_aux {L : Type*} [AddCommGroup L] [Module.Free ℤ L]
    [Module.Finite ℤ L] (E : L →+ L →+ ℤ) (hE : ∀ l, E l l = 0) :
    ∃ χ : L → Circle, ∀ l m, χ (l + m) = χ l * χ m * Circle.exp (Real.pi * E l m) := by
  have hanti : ∀ l m, E m l = -E l m := fun l m => by
    have := hE (l + m)
    simp only [map_add, AddMonoidHom.add_apply, hE] at this
    omega
  let b := Module.finBasis ℤ L
  let EL : LinearMap.BilinForm ℤ L := LinearMap.mk₂ ℤ (fun l m => E l m)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  let F : LinearMap.BilinForm ℤ L :=
    Matrix.toLinearMap₂ b b (Matrix.of fun i j => if i < j then E (b i) (b j) else 0)
  have hF : F - F.flip = EL := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [F, EL, LinearMap.sub_apply, LinearMap.BilinForm.flip_apply,
      Matrix.toLinearMap₂_apply_basis,
      Matrix.of_apply, LinearMap.mk₂_apply]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, hij.not_gt]
    · simp [hE]
    · simp [hij, hij.not_gt, hanti (b j) (b i)]
  have hF' : ∀ l m, F l m = E l m + F m l := fun l m => by
    have := congrArg (fun G : LinearMap.BilinForm ℤ L => G l m) hF
    simp only [LinearMap.sub_apply, LinearMap.BilinForm.flip_apply, EL,
      LinearMap.mk₂_apply] at this
    omega
  refine ⟨fun l => Circle.exp (Real.pi * F l l), fun l m => ?_⟩
  have key : Real.pi * (F (l + m) (l + m) : ℝ) = Real.pi * F l l + Real.pi * F m m +
      Real.pi * E l m + 2 * Real.pi * (F m l : ℤ) := by
    simp only [map_add, LinearMap.add_apply, hF' l m]
    push_cast; ring
  simp only
  rw [key, Circle.exp_add, Circle.exp_two_pi_mul_int, mul_one, Circle.exp_add, Circle.exp_add]

theorem spec_exists_semicharacterOfX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    ∃ χ : abelianPeriodLattice X → Circle, ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m) := by
  let _ : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have := discrete_complexExponentialLattice X (dim X.left)
  have := isZLattice_complexExponentialLattice X (dim X.left)
  have : Module.Free ℤ (abelianPeriodLattice X) := ZLattice.module_free ℝ _
  have : Module.Finite ℤ (abelianPeriodLattice X) := ZLattice.module_finite ℝ _
  have hEl : ∀ l, E l l = 0 := fun l => by
    have h := hE l l
    have him : (H.toFun l l).im = 0 := Complex.conj_eq_iff_im.mp (H.conj_symm l l)
    rw [HermitianForm.imaginary, him] at h
    exact_mod_cast h
  obtain ⟨χ, hχ⟩ := exists_semicharacter_of_alternating_aux E hEl
  exact ⟨χ, fun l m => by rw [hχ, hE]⟩

theorem spec_chernForm_datumOfX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : abelianPeriodLattice X) :
    chernForm f l m = -E l m :=
  (spec_chernForm_holFactor (datumOfX X H E hE χ hχ) f hlog hf l m).trans <| congrArg Neg.neg
    (DFunLike.congr_fun (DFunLike.congr_fun (spec_datumOfX_imForm_aux X H E hE χ hχ) l) m)

/-- The class in `HQ X 2` of the negated form is the negated class, by additivity.
Source: `spec_latticeClassHQ_add`. -/
theorem latticeClassHQ_neg (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    latticeClassHQ X (-E) = -latticeClassHQ X E := by
  have h := spec_latticeClassHQ_add X (-E) E
  rw [neg_add_cancel] at h
  have h0 : latticeClassHQ X 0 = 0 := by
    have h2 := spec_latticeClassHQ_add X 0 0
    rw [add_zero] at h2
    simpa using h2
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_left h.symm

example (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    latticeClassHQ X (-E) + latticeClassHQ X E = 0 := by
  rw [latticeClassHQ_neg, neg_add_cancel]

theorem spec_chernClassHQ_datumOfX_aux (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm f l m) ∧ latticeClassHQ X E' = -latticeClassHQ X E := by
  refine ⟨-E, fun l m => ?_, ?_⟩
  · rw [spec_chernForm_datumOfX_aux X H E hE χ hχ f hlog hf l m]
    simp
  · exact latticeClassHQ_neg X E

theorem spec_chernClassHQ_datumOfX_hardLefschetz_aux
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm f l m) ∧
        HardLefschetz X (cupProductOf X) (latticeClassHQ X E') := by
  obtain ⟨E', hE', hcl⟩ := spec_chernClassHQ_datumOfX_aux X H E hE χ hχ f hlog hf
  refine ⟨E', hE', ?_⟩
  rw [hcl]
  exact (spec_hardLefschetz_neg_iff_aux X (cupProductOf X) _).2
    (spec_latticeClassHQ_hardLefschetz X H hH E hE)

theorem spec_chernClassHQ_trivial_falsification_aux (hg : 0 < dim X.left)
    (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, holFactor (datumOfXTrivial X) l v =
      Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
      (∀ l m, E' l m = chernForm f l m) ∧ latticeClassHQ X E' = 0 ∧
        ¬ HardLefschetz X (cupProductOf X) (latticeClassHQ X E') := by
  have hc : ∀ l m, chernForm f l m = 0 := fun l m => by
    have := spec_chernForm_datumOfX_aux X HermitianForm.zero 0
      (fun _ _ => by simp [HermitianForm.imaginary, HermitianForm.zero]) (fun _ => 1)
      (fun _ _ => by simp [HermitianForm.imaginary, HermitianForm.zero]) f hlog hf l m
    simpa using this
  refine ⟨0, fun l m => by simp [hc], (spec_latticeClassHQ_zero_falsification X hg).1, ?_⟩
  exact (spec_latticeClassHQ_zero_falsification X hg).2

end HodgeLean.Adapters

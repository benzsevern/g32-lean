import HodgeLean.Adapters.RiemannFormHermitianDefs
import HodgeLean.Adapters.AutomorphyChernHQ
import HodgeLean.Foundations.AppellHumbert

/-! # Proofs for the Riemann relations, `H` from `E`

The statements are frozen in `RiemannFormHermitian`; this file proves them. All eleven are proved, by three parallel provers.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass

namespace HodgeLean.Adapters

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

theorem spec_hermitian_toFun_eq_imaginary_aux (H : HermitianForm (V := V)) (v w : V) :
    H.toFun v w = (H.imaginary v (Complex.I • w) : ℂ) + (H.imaginary v w : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [HermitianForm.imaginary, H.smul_right]

theorem rfh_imaginary_real_smul_left (H : HermitianForm (V := V)) (r : ℝ) (x y : V) :
    H.imaginary (r • x) y = r * H.imaginary x y := by
  rw [HermitianForm.imaginary, ← algebraMap_smul ℂ r x, H.smul_left]
  simp [HermitianForm.imaginary]

theorem rfh_imaginary_real_smul_right (H : HermitianForm (V := V)) (r : ℝ) (x y : V) :
    H.imaginary x (r • y) = r * H.imaginary x y := by
  rw [HermitianForm.imaginary, ← algebraMap_smul ℂ r y, H.smul_right]
  simp [HermitianForm.imaginary]

theorem spec_hermitian_imaginary_bilinear_aux (H : HermitianForm (V := V)) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, ∀ v w, B v w = H.imaginary v w :=
  ⟨LinearMap.mk₂ ℝ H.imaginary
    (fun x y z ↦ by simp [HermitianForm.imaginary, H.add_left])
    (fun r x y ↦ by rw [rfh_imaginary_real_smul_left, smul_eq_mul])
    (fun x y z ↦ by simp [HermitianForm.imaginary, H.add_right])
    (fun r x y ↦ by rw [rfh_imaginary_real_smul_right, smul_eq_mul]), fun _ _ ↦ rfl⟩

end Forms

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- Two real-bilinear forms that agree on a full lattice are equal. -/
theorem rfh_realBilin_ext_of_lattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {B B' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : ∀ l m : L, B l m = B' l m) : B = B' := by
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  let bR := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  refine bR.ext fun i ↦ bR.ext fun j ↦ ?_
  simp only [bR, Module.Basis.ofZLatticeBasis_apply]
  exact h _ _

theorem spec_exists_unique_realExtension_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) :
    ∃! B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, ∀ l m : L, B l m = E l m := by
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    bR.constr ℝ fun i ↦ bR.constr ℝ fun j ↦ (E (b i) (b j) : ℝ)
  have hbb : ∀ i j, B (b i) (b j) = E (b i) (b j) := by
    intro i j
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ L b i, ← Module.Basis.ofZLatticeBasis_apply ℝ L b j]
    simp only [B, bR, Module.Basis.constr_basis]
  have hb : ∀ i (m : L), B (b i) m = E (b i) m := by
    intro i
    have := b.ext (f₁ := ((B (b i)).restrictScalars ℤ).comp L.subtype)
      (f₂ := ((Int.castAddHom ℝ).comp (E (b i))).toIntLinearMap) fun j ↦ by
        simpa using hbb i j
    intro m
    simpa using LinearMap.congr_fun this m
  have hBL : ∀ l m : L, B l m = E l m := by
    intro l m
    have := b.ext (f₁ := ((B.flip m).restrictScalars ℤ).comp L.subtype)
      (f₂ := ((Int.castAddHom ℝ).comp (E.flip m)).toIntLinearMap) fun i ↦ by
        simpa using hb i m
    simpa using LinearMap.congr_fun this l
  exact ⟨B, hBL, fun B' hB' ↦ rfh_realBilin_ext_of_lattice L fun l m ↦ by rw [hB', hBL]⟩

theorem spec_realExtension_alternating_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) (hE : ∀ l : L, E l l = 0)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = E l m) (v : V) : B v v = 0 := by
  have hanti : ∀ l m : L, E l m = -E m l := by
    intro l m
    have := hE (l + m)
    simp only [map_add, AddMonoidHom.add_apply, hE l, hE m] at this
    omega
  have hflip : B.flip = -B := rfh_realBilin_ext_of_lattice L fun l m ↦ by
    simp [hB, hanti l m]
  have := LinearMap.congr_fun₂ hflip v v
  simp only [LinearMap.flip_apply, LinearMap.neg_apply] at this
  linarith

omit [FiniteDimensional ℂ V] in
/-- Two real-bilinear forms agreeing on a full lattice are equal. -/
theorem bilin_eq_of_lattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B B' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h : ∀ l m : L, B l m = B' l m) : B = B' := by
  have hs : Submodule.span ℝ (L : Set V) = ⊤ := IsZLattice.span_top
  refine LinearMap.ext_on hs fun x hx ↦ LinearMap.ext_on hs fun y hy ↦ ?_
  exact h ⟨x, hx⟩ ⟨y, hy⟩

theorem spec_hermitian_eq_of_imaginary_lattice_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (H H' : HermitianForm (V := V))
    (h : ∀ l m : L, H.imaginary l m = H'.imaginary l m) : H = H' := by
  obtain ⟨B, hB⟩ := spec_hermitian_imaginary_bilinear_aux H
  obtain ⟨B', hB'⟩ := spec_hermitian_imaginary_bilinear_aux H'
  have hBB : B = B' := bilin_eq_of_lattice L B B' (fun l m ↦ by rw [hB, hB', h])
  have hf : H.toFun = H'.toFun := by
    funext v w
    rw [spec_hermitian_toFun_eq_imaginary_aux H, spec_hermitian_toFun_eq_imaginary_aux H',
      ← hB, ← hB, ← hB', ← hB', hBB]
  cases H; cases H'
  cases hf
  rfl

theorem spec_imaginary_eq_realExtension_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, B l m = E l m) (H : HermitianForm (V := V))
    (hE : ∀ l m : L, (E l m : ℝ) = H.imaginary l m) (v w : V) : H.imaginary v w = B v w := by
  obtain ⟨B₀, hB₀⟩ := spec_hermitian_imaginary_bilinear_aux H
  have : B₀ = B := bilin_eq_of_lattice L B₀ B (fun l m ↦ by rw [hB₀, hB, hE])
  rw [← hB₀, this]

theorem spec_exists_hermitian_iff_riemann_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] (E : L →+ L →+ ℤ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, B l m = E l m) :
    (∃ H : HermitianForm (V := V), ∀ l m : L, (E l m : ℝ) = H.imaginary l m) ↔
      (∀ l : L, E l l = 0) ∧ IsTypeOneOne (fun v w ↦ B v w) := by
  constructor
  · rintro ⟨H, hH⟩
    refine ⟨latticeClassHQ_form_self L H E hH, fun v w ↦ ?_⟩
    have h6 := spec_imaginary_eq_realExtension_aux L E B hB H hH
    simp only
    rw [← h6, ← h6, HermitianForm.imaginary, HermitianForm.imaginary, H.smul_left, H.smul_right,
      ← mul_assoc]
    simp
  · rintro ⟨halt, h11⟩
    have hBalt := spec_realExtension_alternating_aux L E halt B hB
    obtain ⟨H, hH⟩ := (spec_appellHumbert_riemann_relations (fun v w ↦ B v w)
      (fun x y z ↦ by simp) (fun r x y ↦ by simp) (fun x y z ↦ by simp)
      (fun r x y ↦ by simp) hBalt).mpr h11
    exact ⟨H, fun l m ↦ by rw [hH]; exact (hB l m).symm⟩

end Lattice

section Falsification

theorem spec_isTypeOneOne_of_alternating_complex_aux (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ)
    (hB : ∀ v, B v v = 0) : IsTypeOneOne (fun v w ↦ B v w) := by
  have hdecomp : ∀ z : ℂ, z = z.re • (1 : ℂ) + z.im • Complex.I := fun z ↦ by
    apply Complex.ext <;> simp
  have h1 : B 1 1 = 0 := hB 1
  have hI : B Complex.I Complex.I = 0 := hB Complex.I
  have hIone : B Complex.I 1 = -B 1 Complex.I := by
    have := hB (1 + Complex.I)
    simp only [map_add, LinearMap.add_apply, h1, hI] at this
    linarith
  have key₀ : ∀ a b c d : ℝ, B (a • (1 : ℂ) + b • Complex.I) (c • (1 : ℂ) + d • Complex.I) =
      (a * d - b * c) * B 1 Complex.I := by
    intro a b c d
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, hI,
      hIone]
    ring
  have key : ∀ v w : ℂ, B v w = (v.re * w.im - v.im * w.re) * B 1 Complex.I := by
    intro v w
    have := key₀ v.re v.im w.re w.im
    rwa [← hdecomp v, ← hdecomp w] at this
  intro v w
  simp only
  rw [key (Complex.I • v), key v]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem spec_nonRiemann_lattice_falsification_aux :
    let E : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℤ := fun n m ↦ n 0 * m 2 - n 2 * m 0
    (∀ n, E n n = 0) ∧
      (∀ n m, (E n m : ℝ) = (gaussPoint n 0).re * (gaussPoint m 1).re -
        (gaussPoint n 1).re * (gaussPoint m 0).re) ∧
      ¬ ∃ H : HermitianForm (V := Fin 2 → ℂ), ∀ n m,
        (E n m : ℝ) = H.imaginary (gaussPoint n) (gaussPoint m) := by
  intro E
  refine ⟨fun n ↦ by simp only [E]; ring, fun n m ↦ ?_, ?_⟩
  · simp [E, gaussPoint]
  · rintro ⟨H, hH⟩
    have hi : ∀ v w, H.imaginary (Complex.I • v) (Complex.I • w) = H.imaginary v w := by
      intro v w
      simp only [HermitianForm.imaginary, H.smul_left, H.smul_right, ← mul_assoc,
        Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    have h01 : gaussPoint ![0, 1, 0, 0] = Complex.I • gaussPoint ![1, 0, 0, 0] := by
      funext j; fin_cases j <;> simp [gaussPoint]
    have h23 : gaussPoint ![0, 0, 0, 1] = Complex.I • gaussPoint ![0, 0, 1, 0] := by
      funext j; fin_cases j <;> simp [gaussPoint]
    have h1 := hH ![1, 0, 0, 0] ![0, 0, 1, 0]
    have h2 := hH ![0, 1, 0, 0] ![0, 0, 0, 1]
    rw [h01, h23, hi, ← h1] at h2
    simp [E] at h2

end Falsification

section Abelian

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem spec_exists_datumOfX_of_riemann_aux
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
      (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m),
      (∀ v w, H.imaginary v w = B v w) ∧
      ∃ (χ : abelianPeriodLattice X → Circle)
        (hχ : ∀ l m : abelianPeriodLattice X,
          χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m)),
        (datumOfX X H E hE χ hχ).imForm = E := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let := discrete_complexExponentialLattice X (dim X.left)
  let := isZLattice_complexExponentialLattice X (dim X.left)
  obtain ⟨H, hE⟩ :=
    (spec_exists_hermitian_iff_riemann_aux (abelianPeriodLattice X) E B hB).2 ⟨hEalt, h11⟩
  obtain ⟨χ, hχ⟩ := spec_exists_semicharacterOfX X H E hE
  exact ⟨H, hE, spec_imaginary_eq_realExtension_aux (abelianPeriodLattice X) E B hB H hE,
    χ, hχ, spec_datumOfX_imForm X H E hE χ hχ⟩

theorem spec_chernClassHQ_hardLefschetz_of_riemann_aux
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (h11 : IsTypeOneOne (fun v w ↦ B v w))
    (hpos : ∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) :
    HardLefschetz X (cupProductOf X) (latticeClassHQ X E) ∧
      ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
        (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m),
        H.IsPositiveDefinite ∧ (∀ v w, H.imaginary v w = B v w) ∧
        ∀ (χ : abelianPeriodLattice X → Circle)
          (hχ : ∀ l m : abelianPeriodLattice X,
            χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
          (f : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ),
          (∀ l v, holFactor (datumOfX X H E hE χ hχ) l v =
            Complex.exp (2 * Real.pi * Complex.I * f l v)) →
          (∀ l, Continuous (f l)) →
          ∃ E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ,
            (∀ l m, E' l m = chernForm f l m) ∧
              HardLefschetz X (cupProductOf X) (latticeClassHQ X E') := by
  obtain ⟨H, hE, hHB, -⟩ := spec_exists_datumOfX_of_riemann_aux X E hEalt B hB h11
  have hH : H.IsPositiveDefinite := by
    intro v hv
    have h := congrArg Complex.re (spec_hermitian_toFun_eq_imaginary_aux H v v)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
    rw [h, hHB]
    exact hpos v hv
  exact ⟨spec_latticeClassHQ_hardLefschetz X H hH E hE, H, hE, hH, hHB,
    fun χ hχ f hlog hf ↦ spec_chernClassHQ_datumOfX_hardLefschetz X H hH E hE χ hχ f hlog hf⟩

end Abelian

end HodgeLean.Adapters

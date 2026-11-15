import HodgeLean.Adapters.IntersectionProductFibreTor
import HodgeLean.Adapters.IntersectionProductMovingRobertsSmooth

/-! # The complex projective line and `X × ℙ¹`

The two standard charts of `ℙ¹_ℤ` have coordinate rings `ℤ[s₀, s₁]_(sⱼ)` of degree zero, which are
polynomial rings `ℤ[t]` (`a3n_awayEquiv`). Hence `ℙ¹_ℂ = ProjectiveSpace (Fin 2) (Spec ℂ)` is
smooth and integral over `ℂ` (`a3n_P1`), and for a smooth projective integral `X` over `ℂ` the
product `X × ℙ¹` over `ℂ` is smooth, integral, Noetherian and proper over `X` (`a3n_T`).

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5 (standard affine charts of `Proj`)
and Theorem II.8.15; Stacks Project, Tag 01MQ. HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The charts of `ℙ¹_ℤ` -/

section charts

variable (j : Fin 2)

/-- The chart ring `ℤ[s₀, s₁]_(s_j)` in degree zero.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5 (`D₊(f) ≅ Spec S_(f)`). -/
abbrev a3n_A : Type := Away (UniversalGrading.{0} 1) (X j : UniversalRing.{0} 1)

example : a3n_A 0 = a3m_Away1 := rfl

/-- `s_j ↦ 1`, the other coordinate `↦ X`, from `ℤ[s₀, s₁]` to `ℤ[X]`.
Source: Hartshorne, *Algebraic Geometry*, I, §2 (dehomogenization). -/
def a3n_ψ : UniversalRing.{0} 1 →+* Polynomial ℤ :=
  eval₂Hom (Polynomial.C.comp ULift.ringEquiv.toRingHom)
    (fun k => if k = j then 1 else Polynomial.X)

example : a3n_ψ 0 (X 1) = Polynomial.X := by simp [a3n_ψ]

/-- Evaluation at the chart coordinate `s_{1-j}/s_j`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def a3n_ev : Polynomial ℤ →+* a3n_A j :=
  Polynomial.eval₂RingHom (algebraMap ℤ (a3n_A j)) (chartCoordinate j j.rev)

example : a3n_ev 0 Polynomial.X = chartCoordinate 0 1 := by simp [a3n_ev]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem a3n_ev_ψ : (a3n_ev j).comp (a3n_ψ j) =
    eval₂Hom ((fromZeroRingHom (UniversalGrading.{0} 1) (.powers (X j))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin 2) (ULift.{0} ℤ)).symm.toRingHom)
      (chartCoordinate j) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
  · have h1 : (((a3n_ev j).comp (a3n_ψ j)).comp MvPolynomial.C).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom =
        ((eval₂Hom ((fromZeroRingHom (UniversalGrading.{0} 1) (.powers (X j))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin 2) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate j)).comp MvPolynomial.C).comp
            (ULift.ringEquiv (R := ℤ)).symm.toRingHom := RingHom.ext_int _ _
    exact congrArg (fun φ : ℤ →+* a3n_A j => φ c.down) h1
  · fin_cases j <;> fin_cases k <;> simp [a3n_ev, a3n_ψ]

theorem a3n_ev_surjective : Function.Surjective (a3n_ev j) := by
  intro a
  obtain ⟨P, rfl⟩ := a3m_awayCoord_surj 1 j a
  exact ⟨a3n_ψ j P, by rw [← RingHom.comp_apply, a3n_ev_ψ]⟩

theorem a3n_ψ_X_self : a3n_ψ j (X j) = 1 := by
  simp [a3n_ψ]

theorem a3n_ψ_X_rev : a3n_ψ j (X j.rev) = Polynomial.X := by
  fin_cases j <;> simp [a3n_ψ]

set_option backward.isDefEq.respectTransparency.types false in
/-- `ℤ[t] → ℤ[s₀, s₁]_(s_j)`, `t ↦ s_{1-j}/s_j`, is injective. -/
theorem a3n_ev_injective : Function.Injective (a3n_ev j) := by
  have hu : IsUnit (a3n_ψ j (X j)) := by rw [a3n_ψ_X_self]; exact isUnit_one
  let lift1 : Localization.Away (X j : UniversalRing.{0} 1) →+* Polynomial ℤ :=
    Localization.awayLift (a3n_ψ j) (X j) hu
  set f₁ := (lift1.comp (algebraMap (a3n_A j) (Localization.Away (X j : UniversalRing.{0} 1)))).comp
      (a3n_ev j)
  have hcomp : f₁ = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · exact congrArg (fun φ : ℤ →+* Polynomial ℤ => φ n)
        (RingHom.ext_int (f₁.comp Polynomial.C) ((RingHom.id _).comp Polynomial.C))
    · simp only [f₁, RingHom.comp_apply, RingHom.id_apply, a3n_ev, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, HomogeneousLocalization.algebraMap_apply]
      have hv : a3n_ψ j (X j) * 1 = 1 := by rw [a3n_ψ_X_self, one_mul]
      rw [show (chartCoordinate j j.rev).val = Localization.mk (X j.rev : UniversalRing.{0} 1)
          (⟨X j ^ 1, 1, rfl⟩ : Submonoid.powers (X j : UniversalRing.{0} 1)) from rfl,
        show lift1 = Localization.awayLift (a3n_ψ j) (X j) (isUnit_iff_exists_inv.mpr ⟨1, hv⟩)
          from rfl, Localization.awayLift_mk _ _ _ 1 hv 1]
      simp [a3n_ψ_X_rev]
  intro f g h
  have h2 : f₁ f = f₁ g := by simp only [f₁, RingHom.comp_apply, h]
  rwa [hcomp] at h2

/-- `ℤ[t] ≅ ℤ[s₀, s₁]_(s_j)` as `ℤ`-algebras.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def a3n_awayEquiv : Polynomial ℤ ≃ₐ[ℤ] a3n_A j :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (a3n_ev j)
    ⟨a3n_ev_injective j, a3n_ev_surjective j⟩) (fun n => by simp)

example : a3n_awayEquiv 0 Polynomial.X = chartCoordinate 0 1 := by
  simp [a3n_awayEquiv, a3n_ev]

instance a3n_polynomial_smooth : Algebra.Smooth ℤ (Polynomial ℤ) :=
  ⟨inferInstance, inferInstance⟩

instance a3n_A_smooth : Algebra.Smooth ℤ (a3n_A j) :=
  Algebra.Smooth.of_equiv (a3n_awayEquiv j)

end charts

/-! ## The complex projective line -/

section line

/-- The chart ring `ℂ ⊗ ℤ[t]` of `ℙ¹_ℂ` is the polynomial ring `ℂ[t]`.
Source: Mathlib, `polyEquivTensor`; Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def a3n_chartEquiv (j : Fin 2) : Polynomial ℂ ≃ₐ[ℤ] a3m_PnT 1 j :=
  (polyEquivTensor ℤ ℂ).trans (Algebra.TensorProduct.congr AlgEquiv.refl (a3n_awayEquiv j))

instance a3n_chart_isDomain (j : Fin 2) : IsDomain (a3m_PnT 1 j) :=
  (a3n_chartEquiv j).symm.toMulEquiv.isDomain

example : a3n_chartEquiv 0 (Polynomial.C 1) = 1 := map_one _

/-- The open cover of `ℙ¹_ℂ` by its two standard charts.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def a3n_P1Cover : (a3m_Pn 1).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2) (fun j => Spec (a3m_PnT 1 j)) (a3m_Pnκ 1)
    (fun y => by
      obtain ⟨j, hj⟩ := a3m_Pn_cover 1 y
      exact ⟨j, hj⟩)

example (j : Fin 2) : a3n_P1Cover.f j = a3m_Pnκ 1 j := rfl

/-- The chart `Spec (ℂ ⊗ ℤ[t]) → ℙ¹_ℂ` lies over `Spec ℂ` through `ℂ → ℂ ⊗ ℤ[t]`. -/
theorem a3n_chart_toBase (j : Fin 2) :
    a3m_Pnκ 1 j ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ)
        (B := a3n_A j))) := by
  have := a3m_prodChart_fst (𝟙 (Spec ↧ℂ)) (g3c_chartι 1 j)
  rw [Category.comp_id] at this
  exact this

instance a3n_P1_smooth : Smooth (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)) := by
  refine IsZariskiLocalAtSource.of_openCover a3n_P1Cover fun j => ?_
  change Smooth (a3m_Pnκ 1 j ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  rw [a3n_chart_toBase, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap ℂ (TensorProduct ℤ ℂ (a3n_A j))).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

instance a3n_P1_isReduced : IsReduced (a3m_Pn 1) := by
  have : ∀ j, IsReduced (a3n_P1Cover.X j) := fun j => by
    change IsReduced (Spec (a3m_PnT 1 j))
    have : _root_.IsReduced (a3m_PnT 1 j) := isReduced_of_noZeroDivisors
    infer_instance
  exact IsReduced.of_openCover (a3m_Pn 1) a3n_P1Cover

/-- The generic point of the chart `j`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 2.9 (generic points). -/
def a3n_bot (j : Fin 2) : Spec (a3m_PnT 1 j) := ⟨⊥, Ideal.isPrime_bot⟩

example (j : Fin 2) : (a3n_bot j).asIdeal = ⊥ := rfl

theorem a3n_bot_specializes (j : Fin 2) (q : Spec (a3m_PnT 1 j)) : a3n_bot j ⤳ q :=
  (PrimeSpectrum.le_iff_specializes _ _).1 (bot_le (a := q.asIdeal))

theorem a3n_θ_ne_zero (j k : Fin 2) : a3m_Pnθ 1 j (X k) ≠ 0 := by
  intro h
  by_cases hk : k = j
  · subst hk
    rw [a3m_Pnθ_X_self] at h
    have : Nontrivial (a3m_PnT 1 k) := (a3n_chart_isDomain k).toNontrivial
    exact (one_ne_zero : (1 : a3m_PnT 1 k) ≠ 0) h
  · have hk' : k = j.rev := by
      fin_cases j <;> fin_cases k <;> first | rfl | exact (hk rfl).elim
    subst hk'
    have h1 : a3m_Pnθ 1 j (X j.rev) = (a3n_chartEquiv j) (Polynomial.X) := by
      simp [a3m_Pnθ, a3n_chartEquiv, a3n_awayEquiv, a3n_ev]
    rw [h1] at h
    exact Polynomial.X_ne_zero ((a3n_chartEquiv j).injective (h.trans (map_zero _).symm))

/-- The generic point of `ℙ¹_ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 2.9 (generic points). -/
def a3n_η : a3m_Pn 1 := a3m_Pnκ 1 0 (a3n_bot 0)

example : a3n_η = a3m_Pnκ 1 0 (a3n_bot 0) := rfl

theorem a3n_η_specializes (c : a3m_Pn 1) : a3n_η ⤳ c := by
  have h0 : ∀ q, a3n_η ⤳ a3m_Pnκ 1 0 q := fun q =>
    (a3n_bot_specializes 0 q).map (a3m_Pnκ 1 0).continuous
  obtain ⟨j, q, rfl⟩ := a3m_Pn_cover 1 c
  fin_cases j
  · exact h0 q
  · have hb : a3m_Pnκ 1 1 (a3n_bot 1) ∈ Set.range (a3m_Pnκ 1 0) := by
      refine ((a3m_projCharts 1).inter 0 1 (a3n_bot 1)).2 ?_
      change a3m_Pnθ 1 1 (X 0) ∉ (⊥ : Ideal _)
      rw [Ideal.mem_bot]
      exact a3n_θ_ne_zero 1 0
    obtain ⟨q', hq'⟩ := hb
    exact (h0 q').trans (hq' ▸ (a3n_bot_specializes 1 q).map (a3m_Pnκ 1 1).continuous)

instance a3n_P1_irreducible : IrreducibleSpace (a3m_Pn 1) := by
  rw [irreducibleSpace_def]
  have : closure ({a3n_η} : Set (a3m_Pn 1)) = Set.univ :=
    Set.eq_univ_of_forall fun c => specializes_iff_mem_closure.1 (a3n_η_specializes c)
  change IsIrreducible Set.univ
  rw [← this]
  exact isIrreducible_singleton.closure

instance a3n_P1_isIntegral : IsIntegral (a3m_Pn 1) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The complex projective line `ℙ¹_ℂ` over `Spec ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II, §7 (projective space over a field). -/
abbrev a3n_P1 : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))

example : Smooth a3n_P1.hom := inferInstanceAs (Smooth (ProjectiveSpace.toBase (Fin 2) _))

end line

end HodgeLean.Adapters

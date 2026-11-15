import HodgeLean.Adapters.IntersectionProductMoving
import HodgeLean.Adapters.IntersectionProductMovingLine
import HodgeLean.Adapters.IntersectionProductMovingRobertsChoice

/-! # The projective variety, `X × ℙ¹` and their homogeneous primes

For an integral projective `X` over `ℂ`, a projective presentation `X ↪ ℙᴺ` gives projective charts
on `X` (`a3s_CX`): the points of `X` are the relevant homogeneous primes of `ℂ[x_0, …, x_N]`
containing the ideal `I_X` of `X` (`a3s_exists_point`), and heights are cone dimensions minus one
(`a3s_height_add_one`). On `T = X × ℙ¹` the open part `X × 𝔸¹` has the line charts of
`a3m_lineCharts`, whose points are the primes `a3s_Q y` of `ℂ[x][t]`: specialization is
inclusion, the point of `X` below `y` has prime `{F | F ∈ a3s_Q y}`, and the fibres over
`t = 0` and `t = 1` are cut out by `t` and `t - 1` (`a3s_fst_prime`, `a3s_mem_Z0`,
`a3s_mem_Zinf`); every relevant `x`-homogeneous prime containing `I_X` is a point
(`a3s_exists_point_U`).

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5, Exercise 3.20 and §II.7.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

section XCharts

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

/-- A projective presentation of `X`. -/
def a3s_pres : ProjectiveSpace.Presentation X.hom :=
  (IsProjective.nonempty_presentation (f := X.hom)).some

/-- The dimension of the ambient projective space. -/
abbrev a3s_N : ℕ := (a3s_pres X).ambientDimension

/-- The closed immersion `X → ℙᴺ`. -/
def a3s_i : X.left ⟶ a3m_Pn (a3s_N X) := (a3s_pres X).immersion

instance : IsClosedImmersion (a3s_i X) := (a3s_pres X).isClosedImmersion

/-- The projective charts of `X`, restricted from `ℙᴺ`. -/
def a3s_CX : a3m_SpecCharts X.left (Fin (a3s_N X + 1)) ℂ :=
  (a3m_projCharts (a3s_N X)).restrict (a3s_i X)

/-- The ideal of `X` in the homogeneous coordinate ring. -/
abbrev a3s_IX : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ) := (a3s_CX X).prime (genericPoint X.left)

instance : (a3s_IX X).IsPrime := (a3s_CX X).isPrime_prime _

theorem a3s_IX_isHomogeneous :
    (a3s_IX X).IsHomogeneous (homogeneousSubmodule (Fin (a3s_N X + 1)) ℂ) :=
  (a3s_CX X).isHomogeneous_prime _

omit [IsIntegral X.left] in
/-- Heights of points of `X` are dimensions of affine cones, minus one. -/
theorem a3s_height_add_one (x : X.left) :
    (Order.height x : WithBot ℕ∞) + 1 =
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ (a3s_CX X).prime x) := by
  let _ : ∀ j, Algebra ℂ ((a3s_CX X).T j) := fun j => (((a3s_CX X).θ j).comp C).toAlgebra
  exact a3m_SpecCharts.height_add_one (Y := X) (a3s_CX X) (fun _ _ => rfl) x

omit [IsIntegral X.left] in
theorem a3s_relevant (x : X.left) : ∃ j, MvPolynomial.X j ∉ (a3s_CX X).prime x :=
  ⟨(a3s_CX X).chart x, fun h => ((a3s_CX X).X_mem_prime_iff x _).1 h ((a3s_CX X).mem_chart x)⟩

theorem a3s_IX_le (x : X.left) : a3s_IX X ≤ (a3s_CX X).prime x :=
  (a3s_CX X).prime_mono (genericPoint_specializes x)

/-- Relevant homogeneous primes containing `I_X` are the points of `X`. -/
theorem a3s_exists_point (P : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin (a3s_N X + 1)) ℂ)) (j : Fin (a3s_N X + 1))
    (hj : MvPolynomial.X j ∉ P) (hXP : a3s_IX X ≤ P) : ∃ x, (a3s_CX X).prime x = P :=
  (a3s_CX X).exists_prime_eq P hP j hj hXP

end XCharts

/-! ## The total space `X × ℙ¹` -/

section Total

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

instance a3s_P1_proper : IsProper (terminal.from (g3c_P 1)) :=
  ProjectiveSpace.terminalProjProper (Fin 2)

/-- The projection `X × ℙ¹ → X`. -/
abbrev a3s_fst : a3m_T X.left ⟶ X.left := pullback.fst (terminal.from X.left) (terminal.from (g3c_P 1))

/-- The projection `X × ℙ¹ → ℙ¹`. -/
abbrev a3s_snd : a3m_T X.left ⟶ g3c_P 1 :=
  pullback.snd (terminal.from X.left) (terminal.from (g3c_P 1))

/-- `X × ℙ¹` over `ℂ`. -/
abbrev a3s_T : Over (Spec ↧ℂ) := Over.mk (a3s_fst X ≫ X.hom)

instance a3s_T_lft : LocallyOfFiniteType (a3s_T X).hom := by
  change LocallyOfFiniteType (a3s_fst X ≫ X.hom); infer_instance

instance a3s_T_qc : QuasiCompact (a3s_T X).hom := by
  change QuasiCompact (a3s_fst X ≫ X.hom); infer_instance

/-- The projection as a morphism over `ℂ`. -/
def a3s_q : a3s_T X ⟶ X := Over.homMk (a3s_fst X) rfl

instance a3s_q_proper : IsProper (a3s_q X).left := by
  change IsProper (a3s_fst X); infer_instance

instance a3s_T_noeth : IsNoetherian (a3s_T X).left := inferInstance

omit [IsIntegral X.left] in
theorem a3s_hov (j l : Fin (a3s_N X + 1)) (F : MvPolynomial (Fin (a3s_N X + 1)) ℂ) (e : ℕ)
    (hF : F.IsHomogeneous e) :
    (pullback.snd ((a3s_CX X).κ j) ((a3s_CX X).κ l)).appTop
        ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ l F)) =
      (pullback.snd ((a3s_CX X).κ j) ((a3s_CX X).κ l)).appTop
          ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ l (MvPolynomial.X j))) ^ e *
        (pullback.fst ((a3s_CX X).κ j) ((a3s_CX X).κ l)).appTop
          ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ j F)) :=
  a3m_restrict_hov (a3m_projCharts (a3s_N X)) (a3s_i X) (a3m_Pn_hov (a3s_N X)) j l F e hF

/-- The projective charts of `X × 𝔸¹`. -/
def a3s_LC : a3m_SpecCharts (a3m_U X.left).toScheme (Fin (a3s_N X + 1)) (Polynomial ℂ) :=
  a3m_lineCharts (a3s_CX X) (a3s_hov X)

/-- `X × 𝔸¹` over `ℂ`. -/
abbrev a3s_Uo : Over (Spec ↧ℂ) := Over.mk ((a3m_U X.left).ι ≫ (a3s_T X).hom)

instance : LocallyOfFiniteType (a3s_Uo X).hom := by
  change LocallyOfFiniteType ((a3m_U X.left).ι ≫ (a3s_T X).hom); infer_instance

omit [IsIntegral X.left] in
/-- Heights of points of `X × 𝔸¹` are dimensions of their cones. -/
theorem a3s_height_add_one_U (y : (a3m_U X.left).toScheme) :
    (Order.height y : WithBot ℕ∞) + 1 =
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) (Polynomial ℂ) ⧸ (a3s_LC X).prime y) := by
  let _ : ∀ j, Algebra ℂ ((a3s_LC X).T j) := fun j =>
    (((a3s_LC X).θ j).comp (algebraMap ℂ (MvPolynomial (Fin (a3s_N X + 1)) (Polynomial ℂ)))).toAlgebra
  exact a3m_SpecCharts.height_add_one (Y := a3s_Uo X) (a3s_LC X) (fun _ _ => rfl) y

omit [IsIntegral X.left] in
/-- Heights in `X × 𝔸¹` agree with heights in `X × ℙ¹`. -/
theorem a3s_height_U (y : (a3m_U X.left).toScheme) :
    Order.height ((a3m_U X.left).ι y) = Order.height y := by
  obtain ⟨j, p, hp⟩ := (a3s_LC X).cover y
  rw [← hp, a3m_height_openImmersion (Y := a3s_Uo X) ((a3s_LC X).κ j) p]
  have : (a3m_U X.left).ι ((a3s_LC X).κ j p) = a3m_Tκ (a3s_CX X) j p := by
    have h := a3m_lineCharts_κ (a3s_CX X) (a3s_hov X) j
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : Spec _ ⟶ _ => f p) h
  rw [this]
  exact a3m_height_openImmersion (Y := a3s_T X) (a3m_Tκ (a3s_CX X) j) p

/-- The prime of `B[t]` of a point of `X × 𝔸¹`. -/
def a3s_Q (y : (a3m_U X.left).toScheme) :
    Ideal (Polynomial (MvPolynomial (Fin (a3s_N X + 1)) ℂ)) :=
  ((a3s_LC X).prime y).comap (a3m_eq (Fin (a3s_N X + 1)))

instance (y : (a3m_U X.left).toScheme) : (a3s_Q X y).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsIntegral X.left] in
theorem a3s_Q_le_iff (y y' : (a3m_U X.left).toScheme) : a3s_Q X y ≤ a3s_Q X y' ↔ y ⤳ y' := by
  rw [← (a3s_LC X).prime_le_iff, a3s_Q, a3s_Q]
  constructor
  · intro h G hG
    obtain ⟨H, rfl⟩ := (a3m_eq (Fin (a3s_N X + 1))).surjective G
    exact h hG
  · intro h H hH
    exact h hH

omit [IsIntegral X.left] in
theorem a3s_dim_Q (y : (a3m_U X.left).toScheme) :
    ringKrullDim (Polynomial (MvPolynomial (Fin (a3s_N X + 1)) ℂ) ⧸ a3s_Q X y) =
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) (Polynomial ℂ) ⧸ (a3s_LC X).prime y) := by
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _
    (a3m_eq (Fin (a3s_N X + 1))).toRingEquiv ?_)
  rw [a3s_Q]
  exact (Ideal.map_comap_of_surjective _ (a3m_eq (Fin (a3s_N X + 1))).toRingEquiv.surjective _).symm

omit [IsIntegral X.left] in
/-- The point of `X` under a point of `X × 𝔸¹`. -/
theorem a3s_fst_prime (y : (a3m_U X.left).toScheme) (F : MvPolynomial (Fin (a3s_N X + 1)) ℂ) :
    F ∈ (a3s_CX X).prime (a3s_fst X ((a3m_U X.left).ι y)) ↔ Polynomial.C F ∈ a3s_Q X y := by
  rw [a3m_line_prime_fst (a3s_CX X) (a3s_hov X) y, Ideal.mem_comap, a3s_Q, Ideal.mem_comap,
    a3m_eq_C]
  rfl

omit [IsIntegral X.left] in
theorem a3s_mem_Z0 (y : (a3m_U X.left).toScheme) :
    a3s_snd X ((a3m_U X.left).ι y) ∈ a3m_Z0 ↔ Polynomial.X ∈ a3s_Q X y := by
  rw [a3m_line_mem_Z0 (a3s_CX X) (a3s_hov X) y, a3s_Q, Ideal.mem_comap, a3m_eq_X]
  rfl

omit [IsIntegral X.left] in
theorem a3s_mem_Zinf (y : (a3m_U X.left).toScheme) :
    a3s_snd X ((a3m_U X.left).ι y) ∈ a3m_Zinf ↔ Polynomial.X - 1 ∈ a3s_Q X y := by
  rw [a3m_line_mem_Zinf (a3s_CX X) (a3s_hov X) y, a3s_Q, Ideal.mem_comap]
  have : a3m_eq (Fin (a3s_N X + 1)) (Polynomial.X - 1) = MvPolynomial.C (Polynomial.X - 1) := by
    rw [map_sub, map_one, a3m_eq_X, map_sub, map_one]
  rw [this]
  rfl

/-- A prime of `B[t]`, homogeneous in `x`, relevant and containing `I_X`, is a point of
`X × 𝔸¹`. -/
theorem a3s_exists_point_U (Qp : Ideal (Polynomial (MvPolynomial (Fin (a3s_N X + 1)) ℂ)))
    [Qp.IsPrime]
    (hhom : (Qp.map (a3m_eq (Fin (a3s_N X + 1)))).IsHomogeneous
      (homogeneousSubmodule (Fin (a3s_N X + 1)) (Polynomial ℂ)))
    (j : Fin (a3s_N X + 1)) (hj : Polynomial.C (MvPolynomial.X j) ∉ Qp)
    (hjX : MvPolynomial.X j ∉ a3s_IX X) (hXQ : Ideal.map Polynomial.C (a3s_IX X) ≤ Qp) :
    ∃ y, a3s_Q X y = Qp := by
  classical
  set e := a3m_eq (Fin (a3s_N X + 1))
  have hP : (Qp.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have hcomap : (Qp.map e).comap e = Qp := Ideal.comap_map_of_bijective _ e.bijective
  -- the point of the chart `j` over the generic point of `X`
  obtain ⟨p, hp⟩ : genericPoint X.left ∈ Set.range ((a3s_CX X).κ j) := by
    by_contra h
    exact hjX (((a3s_CX X).X_mem_prime_iff _ j).2 h)
  obtain ⟨y, hy⟩ := (a3s_LC X).exists_prime_eq' (Qp.map e) hhom j (by
      intro h
      apply hj
      rw [← hcomap, Ideal.mem_comap]
      convert h using 1
      rw [a3m_eq_C]
      simp) (fun G d hG hθ => by
      obtain ⟨H, rfl⟩ := e.surjective G
      have h0 : ∀ i, (a3s_CX X).θ j (H.coeff i) = 0 :=
        (a3m_Tθ_eq_zero_iff (a3s_CX X) j H).1 hθ
      have hH : H ∈ Qp := by
        refine hXQ (Ideal.mem_map_C_iff.2 fun i => ?_)
        refine ((a3s_CX X).mem_prime_iff_of_isHomogeneous _ j p hp _ d
          (a3m_isHomogeneous_coeff H d hG i)).2 ?_
        rw [h0 i]
        exact zero_mem _
      exact Ideal.mem_map_of_mem _ hH)
  exact ⟨y, by rw [a3s_Q, hy, hcomap]⟩

end Total

end HodgeLean.Adapters

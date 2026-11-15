import HodgeLean.Foundations.AnalyticGermExtensionProofs

/-! # Analytic extension preparation

Implication from finite local parameter maps to representative coordinate equations,
and from bounded punctured holomorphy to extension at a point; parameter calibration.
Image surjectivity, component comparison and point Remmert–Stein remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, III.C, dimension of the convergent power series ring. -/
theorem adim6_parameter_dimension (n : ℕ) :
    ringKrullDim (AnalyticGerm n) = (n : WithBot ℕ∞) :=
  adim6_parameter_dimension_aux n

/-- Source: Grauert--Remmert, Coherent Analytic Sheaves, Chapter 5, representatives of finite local analytic algebras; Gunning--Rossi, III.C. -/
theorem adim6_representative_equations (n d m : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (k : Fin n → ℕ) (a : (j : Fin n) → Fin (k j) → (Fin d → ℂ) → ℂ)
      (W : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)),
      (∀ j, 0 < k j) ∧ (∀ j i, AnalyticOnNhd ℂ (a j i) V) ∧
      (∀ j i, a j i 0 = 0) ∧ IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧ π '' W ⊆ V ∧
      ∀ z ∈ W, (∀ l, f l z = 0) → ∀ j,
        z j ^ k j + ∑ i : Fin (k j), a j i (π z) * z j ^ (i : ℕ) = 0 :=
  adim6_representative_equations_aux n d m P hP π θ hfinite hcomp g hgen f U hU hU0 hf hrep

/-- Source: Gunning--Rossi, III.C, finite representatives and root confinement; Chirka, Complex Analytic Sets, §3. -/
theorem adim6_confined_projection (n d m : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)),
      IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∃ p : {z : Fin n → ℂ // z ∈ W ∧ ∀ j, f j z = 0} → V,
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧
        ∀ z, (p z).val = 0 → z.val = 0 :=
  adim6_confined_projection_aux n d m P hP π θ hfinite hcomp g hgen f U hU hU0 hf hrep

/-- Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, I.A and III.C, Cauchy formula and removable singularities; Mathlib.Analysis.Complex.RemovableSingularity. -/
theorem adim6_bounded_point_extension (d : ℕ) (U : Set (Fin (d + 1) → ℂ))
    (hU : IsOpen U) (hU0 : (0 : Fin (d + 1) → ℂ) ∈ U)
    (f : (Fin (d + 1) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {0}))
    (hbounded : ∃ C : ℝ, ∀ z ∈ U \ {0}, ‖f z‖ ≤ C) :
    AnalyticOnNhd ℂ (Function.update f 0 (limUnder (𝓝[≠] 0) f)) U :=
  adim6_bounded_point_extension_aux d U hU hU0 f hf hbounded

/-- W1: the full two-dimensional germ has dimension two.
Source: Gunning--Rossi, III.C, coordinate dimension. -/
example : ringKrullDim (AnalyticGerm 2) = (2 : WithBot ℕ∞) :=
  adim6_parameter_dimension 2

/-- W2: the identity parameter map on a line supplies every representative input.
Source: Gunning--Rossi, III.C, finite parameter maps. -/
example : ∃ (k : Fin 1 → ℕ)
    (a : (j : Fin 1) → Fin (k j) → (Fin 1 → ℂ) → ℂ)
    (W V : Set (Fin 1 → ℂ)),
    (∀ j, 0 < k j) ∧ (∀ j i, AnalyticOnNhd ℂ (a j i) V) ∧
    (∀ j i, a j i 0 = 0) ∧ IsOpen W ∧ (0 : Fin 1 → ℂ) ∈ W ∧ W ⊆ univ ∧
    IsOpen V ∧ (0 : Fin 1 → ℂ) ∈ V ∧ W ⊆ V ∧
    ∀ z ∈ W, ∀ j, z j ^ k j + ∑ i : Fin (k j), a j i z * z j ^ (i : ℕ) = 0 := by
  have hcomp : ∀ (a : AnalyticGerm 1) (f : (Fin 1 → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm 1),
      Germ.ofFun (fun z ↦ f ((ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) z)) = b.val →
        Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) a = Ideal.Quotient.mk ⊥ b := by
    intro a f _ ha b hb
    have hab : a = b := Subtype.ext (ha.symm.trans hb)
    rw [hab]
  have hgen : Ideal.span (Set.range (fun j : Fin 0 ↦ Fin.elim0 j : Fin 0 → AnalyticGerm 1)) = ⊥ := by
    simp
  simpa using adim6_representative_equations 1 1 0 ⊥ bot_ne_top
    (ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) (Ideal.Quotient.mk ⊥)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hcomp
    (fun j : Fin 0 ↦ Fin.elim0 j) hgen (fun j : Fin 0 ↦ Fin.elim0 j)
    univ isOpen_univ (mem_univ _) (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)

/-- W3: a nonconstant coordinate with a corrupted value at the missing point.
Source: Gunning--Rossi, I.A, removable singularities and Cauchy extension. -/
example : ∃ F : (Fin 2 → ℂ) → ℂ,
    AnalyticOnNhd ℂ F (Metric.ball 0 1) ∧
    Set.EqOn F (fun z ↦ if z = 0 then 7 else z 0) (Metric.ball 0 1 \ {0}) := by
  refine ⟨Function.update (fun z : Fin 2 → ℂ ↦ if z = 0 then 7 else z 0) 0
    (limUnder (𝓝[≠] 0) (fun z : Fin 2 → ℂ ↦ if z = 0 then 7 else z 0)), ?_, ?_⟩
  · apply adim6_bounded_point_extension 1 (Metric.ball 0 1) Metric.isOpen_ball
      (Metric.mem_ball_self (by norm_num))
    · apply AnalyticOnNhd.congr (Metric.isOpen_ball.sdiff isClosed_singleton)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticOnNhd _)
      intro z hz
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hz
      simp [hz.2]
    · refine ⟨1, ?_⟩
      intro z hz
      have hne : z ≠ 0 := hz.2
      simp only [ite_eq_right hne]
      have hz' : ‖z‖ < 1 := by simpa using hz.1
      exact (norm_le_pi_norm z 0).trans hz'.le

  · intro z hz
    exact Function.update_of_ne hz.2 _ _

/-- W4: the identity map on a line has a proper confined representative with singleton fibres.
Source: Gunning--Rossi, III.C, finite local projections. -/
example : ∃ (W V : Set (Fin 1 → ℂ)),
    IsOpen W ∧ (0 : Fin 1 → ℂ) ∈ W ∧ W ⊆ univ ∧
    IsOpen V ∧ (0 : Fin 1 → ℂ) ∈ V ∧
    ∃ p : {z : Fin 1 → ℂ // z ∈ W ∧
      ∀ j : Fin 0, (Fin.elim0 j : (Fin 1 → ℂ) → ℂ) z = 0} → V,
      (∀ z, (p z).val = z.val) ∧ IsProperMap p ∧
      (∀ w : V, (p ⁻¹' {w}).Finite) ∧ ∀ z, (p z).val = 0 → z.val = 0 := by
  have hcomp : ∀ (a : AnalyticGerm 1) (f : (Fin 1 → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm 1),
      Germ.ofFun (fun z ↦ f ((ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) z)) = b.val →
        Ideal.Quotient.mk (⊥ : Ideal (AnalyticGerm 1)) a = Ideal.Quotient.mk ⊥ b := by
    intro a f _ ha b hb
    have hab : a = b := Subtype.ext (ha.symm.trans hb)
    rw [hab]
  have hgen : Ideal.span (Set.range (fun j : Fin 0 ↦ Fin.elim0 j : Fin 0 → AnalyticGerm 1)) = ⊥ := by
    simp
  simpa using adim6_confined_projection 1 1 0 ⊥ bot_ne_top
    (ContinuousLinearMap.id ℂ (Fin 1 → ℂ)) (Ideal.Quotient.mk ⊥)
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hcomp
    (fun j : Fin 0 ↦ Fin.elim0 j) hgen (fun j : Fin 0 ↦ Fin.elim0 j)
    univ isOpen_univ (mem_univ _) (by intro j; exact Fin.elim0 j)
    (by intro j; exact Fin.elim0 j)

end HodgeLean.Foundations

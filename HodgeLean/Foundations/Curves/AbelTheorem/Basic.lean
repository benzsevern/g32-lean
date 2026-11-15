import HodgeLean.Foundations.Curves.AbelTheorem.Proofs

/-! # Public interfaces for Abel's theorem

The wrappers retain the literal auxiliary signatures.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Source: Farkas–Kra, Riemann Surfaces, III.2; Griffiths–Harris, Principles of Algebraic Geometry, 2.2.
HC no distance; AV milestone no distance.
-/
theorem normalizedBilinear (h : Module.finrank ℂ E = 1) (p : C) (D : C →₀ ℤ) :
    ∃ F : PeriodFrame (E := E) D,
      (∀ i j, loopIntegral (F.b i) (F.forms j) = loopIntegral (F.b j) (F.forms i)) ∧
      ∀ z : Fin F.genus → ℂ, z ≠ 0 →
        0 < Complex.im (∑ i, ∑ j,
          star (z i) * loopIntegral (F.b i) (F.forms j) * z j) :=
  normalizedBilinear_aux h p D

example : ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic,
    loopIntegral b3A_loopA θ = 1 ∧ loopIntegral b3A_loopB θ = Complex.I :=
  b3_elliptic_periods b3A_loopA b3A_loopB rfl rfl

/-- Source: Miranda, Algebraic Curves and Riemann Surfaces, VIII.2; Farkas–Kra, Riemann Surfaces, III.6.
HC no distance; AV milestone no distance.
-/
theorem principalReciprocity (h : Module.finrank ℂ E = 1) (p : C)
    (f : b4c_MeroFun E C) (hf : ∃ x, f x ≠ (0 : ℂ))
    (paths : C → ℝ → C) (hp : ∀ x, b3A_IsGoodPath (E := E) (paths x) p x) :
    ∃ ell : b3_periodLattice E C,
      ∀ θ : b3_HolForm E C, divisorIntegral (E := E) (b4c_div E f) paths θ = ell.val θ :=
  principalReciprocity_aux h p f hf paths hp

example : divisorIntegral (E := b3_EllipticModel)
    (Finsupp.single (0 : b3_Elliptic) (1 : ℤ)) (fun _ => b3A_loopA.val) b3A_dz = 1 := by
  classical
  simp only [divisorIntegral, Finsupp.sum_single_index, Int.cast_one, one_mul,
    Int.cast_zero, zero_mul]
  change b3_pathPeriod _ _ b3_ellipticA b3A_dz = 1
  rw [b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e0]

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, normalized differentials of the third kind.
HC no distance; AV milestone no distance.
-/
theorem normalizedThirdKind (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (F : PeriodFrame (E := E) D) :
    ∃ w : b4c_MeroForm E C h,
      (∀ x, b4c_res (hE := h) w x = (D x : ℂ)) ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0) ∧
      (∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0) ∧
      ∀ i, loopIntegral (F.a i) w = 0 :=
  normalizedThirdKind_aux h p D hdeg F

example : ∃ w : b4c_MeroForm b3_EllipticModel b3_Elliptic b3_ellipticModel_finrank,
    ∀ x, b4c_res (hE := b3_ellipticModel_finrank) w x =
      ((Finsupp.single (b3_ellipticPoint (1 / 3 : ℝ) 0) (1 : ℤ) -
        Finsupp.single (0 : b3_Elliptic) (1 : ℤ)) x : ℂ) := by
  letI ellipticConnected : ConnectedSpace b3_Elliptic := b3_elliptic_connectedSpace
  obtain ⟨w, hw, _, _⟩ := thirdKindDifferential_supported_on_divisor
    b3_ellipticModel_finrank (0 : b3_Elliptic)
    (Finsupp.single (b3_ellipticPoint (1 / 3 : ℝ) 0) (1 : ℤ) -
      Finsupp.single (0 : b3_Elliptic) (1 : ℤ))
    (by simp [b4c_deg, Finsupp.sum_sub_index])
  exact ⟨w, hw⟩

/-- Source: Griffiths–Harris, Principles of Algebraic Geometry, 2.2, proof of Abel theorem; Farkas–Kra, Riemann Surfaces, III.6.
HC no distance; AV milestone no distance.
-/
theorem thirdKindPeriods (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) (F : PeriodFrame (E := E) D)
    (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (hn : ∀ i, loopIntegral (F.a i) w = 0)
    (hzero : weightedSum (analyticAbel h p) D = 0) :
    ∃ (ell : b3_periodLattice E C) (v : b4c_MeroForm E C h),
      (∀ i, loopIntegral (F.b i) w = (2 * Real.pi * Complex.I) * ell.val (F.forms i)) ∧
      ((v : TangentBundle 𝓘(ℂ, E) C → ℂ) =
        (w : TangentBundle 𝓘(ℂ, E) C → ℂ) -
          (2 * Real.pi * Complex.I) • ∑ i : Fin F.genus,
            ((F.latticeBasis.repr ell (Sum.inr i) : ℤ) : ℂ) •
              (F.forms i : TangentBundle 𝓘(ℂ, E) C → ℂ)) ∧
      (∀ x, b4c_res (hE := h) v x = (D x : ℂ)) ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h v x) 0) ∧
      ∃ hav : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h v x) 0,
        ∀ γ : b3_SmoothLoop E (divisorComplement D),
          Complex.exp (b3_period E (divisorComplement D) γ
            (divisorDifferentialRestriction h D v hav)) = 1 :=
  thirdKindPeriods_aux h p D hdeg F w hr ho ha hn hzero

example : ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic,
    loopIntegral b3A_loopA θ = 1 ∧
      Complex.exp ((2 * Real.pi * Complex.I) * loopIntegral b3A_loopA θ) = 1 := by
  obtain ⟨θ, ha, _⟩ := b3_elliptic_periods b3A_loopA b3A_loopB rfl rfl
  refine ⟨θ, ha, ?_⟩
  change Complex.exp ((2 * Real.pi * Complex.I) * b3_period _ _ b3A_loopA θ) = 1
  rw [ha, mul_one]
  exact Complex.exp_eq_one_iff.mpr ⟨1, by simp⟩

/-- Source: Miranda, Algebraic Curves and Riemann Surfaces, VIII.2; Forster, Lectures on Riemann Surfaces, §§10, 18, 21.
HC no distance; AV milestone no distance.
-/
theorem singleValuedPrimitive (h : Module.finrank ℂ E = 1) (D : C →₀ ℤ)
    (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (p : divisorComplement D)
    (hperiod : ∀ γ : b3_SmoothLoop E (divisorComplement D),
      Complex.exp (b3_period E (divisorComplement D) γ
        (divisorDifferentialRestriction h D w ha)) = 1) :
    ∃ f : C → ℂ,
      ContinuousOn f (divisorComplement D : Set C) ∧
      (∀ x, x ∉ D.support → f x ≠ 0) ∧
      (∀ (q : divisorComplement D) (γ : ℝ → divisorComplement D),
        b3A_IsGoodPath (E := E) γ p q →
          f q.val = exponentialIntegral (E := E) γ (divisorDifferentialRestriction h D w ha)) ∧
      ∀ x, ∀ᶠ z in 𝓝[≠] 0,
        centeredScalar h f x z ≠ 0 ∧
          HasDerivAt (centeredScalar h f x)
            (HurwitzPrymRR_loc h w x z * centeredScalar h f x z) z :=
  singleValuedPrimitive_aux h D w ha p hperiod

example : centeredScalar b3_ellipticModel_finrank
    (fun _ : b3_Elliptic => (2 : ℂ)) (0 : b3_Elliptic) 0 ≠ 0 := by
  norm_num [centeredScalar]

/-- Source: Griffiths–Harris, Principles of Algebraic Geometry, 2.2, Abel theorem; Miranda, Algebraic Curves and Riemann Surfaces, VIII.2.
HC no distance; AV milestone no distance.
-/
theorem abelConverse (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0)
    (hperiod : weightedSum (analyticAbel h p) D = 0) :
    ∃ f : b4c_MeroFun E C, (∃ x, f x ≠ (0 : ℂ)) ∧ b4c_div E f = D :=
  abelConverse_aux h p D hdeg hperiod

example : ∃ f : b4c_MeroFun b3_EllipticModel b3_Elliptic,
    (∃ x, f x ≠ (0 : ℂ)) ∧ b4c_div b3_EllipticModel f = 0 := by
  letI ellipticConnected : ConnectedSpace b3_Elliptic := b3_elliptic_connectedSpace
  letI sphereCharted : ChartedSpace ℂ (OnePoint ℂ) := b4cov_sphChartedSpace
  letI sphereManifold : IsManifold 𝓘(ℂ, ℂ) ω (OnePoint ℂ) := b4cov_sph_isManifold
  let f : b4c_MeroFun b3_EllipticModel b3_Elliptic :=
    ⟨fun _ => ((1 : ℂ) : OnePoint ℂ), contMDiff_const, (0 : b3_Elliptic), OnePoint.coe_ne_infty (1 : ℂ)⟩
  have hf : ∃ x, f x ≠ (0 : ℂ) :=
    ⟨0, OnePoint.coe_injective.ne (one_ne_zero : (1 : ℂ) ≠ 0)⟩
  exact ⟨f, hf, meromorphic_divisor_eq_zero_of_constant f hf (fun _ _ => rfl)⟩

-- The original converse signature follows from the period stages and the retained extension theorem.
example (h : Module.finrank ℂ E = 1) (p : C)
    (D : C →₀ ℤ) (hdeg : b4c_deg D = 0)
    (hperiod : weightedSum (analyticAbel h p) D = 0) :
    ∃ f : b4c_MeroFun E C, (∃ x, f x ≠ (0 : ℂ)) ∧ b4c_div E f = D := by
  classical
  obtain ⟨F, _, _⟩ := normalizedBilinear h p D
  obtain ⟨w, hr, ho, ha, hn⟩ := normalizedThirdKind h p D hdeg F
  obtain ⟨ell, v, _, _, hrv, hov, hav, hpv⟩ :=
    thirdKindPeriods h p D hdeg F w hr ho ha hn hperiod
  obtain ⟨q, hq⟩ := RiemannRochAna_exists_unmarked h p (fun x : D.support => x.val)
  have hqs : q ∉ D.support := fun hx => hq ⟨⟨q, hx⟩, rfl⟩
  obtain ⟨f, hc, hne, _, hs⟩ := singleValuedPrimitive h D v hav ⟨q, hqs⟩ hpv
  exact meromorphicFunction_of_logarithmic_solution h D v hrv hov f hs q
    (hc.continuousAt ((divisorComplement D).isOpen.mem_nhds hqs)) (hne q hqs)

end HodgeLean.Foundations.Curves.AbelTheorem

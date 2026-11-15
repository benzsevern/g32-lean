import HodgeLean.Foundations.Program.CurveJacobianATorus

/-! # Track B3, lane A: explicit computations on the elliptic curve `ℂ ⧸ (ℤ + iℤ)`

The classes `[e₀]`, `[e₁] = i [e₀]` of `(ℂ ⊗ ℤ²) ⧸ F`, the coordinate `z` (`b3A_φ`), the loops
`a`, `b` as straight lines, the form `dz`, and from these: `dim Ω¹ = 1`, the periods `1` and `i` of
`dz`, transversality and intersection number `1` of `a` and `b`, and the explicit values of an
Abel–Jacobi map based at `0`.
-/

noncomputable section

open Manifold Filter Topology
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Elliptic

/-- The classes `[e₀]`, `[e₁]` in `(ℂ ⊗ ℤ²) ⧸ F`. -/
def b3A_e (i : Fin 2) : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF :=
  b2_latticeMap _ b2_stdF (Pi.single i 1)

/-- `[e₁] = i [e₀]`. -/
theorem b3A_e_one : b3A_e 1 = Complex.I • b3A_e 0 := by
  rw [b3A_e, b3A_e, b2_latticeMap, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearMap.toAddMonoidHom_coe, ← map_smul, ← sub_eq_zero,
    ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have : b2_incl (Fin 2 → ℤ) (Pi.single 1 1) - Complex.I • b2_incl (Fin 2 → ℤ) (Pi.single 0 1) =
      (-Complex.I) • ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) +
        Complex.I ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ)) := by
    show (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ) -
      Complex.I • ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ)) = _
    simp only [smul_add, TensorProduct.smul_tmul', smul_eq_mul, mul_one, neg_mul,
      Complex.I_mul_I, neg_neg, TensorProduct.neg_tmul]
    abel
  rw [this]
  exact b2_stdF.smul_mem _ (Submodule.mem_span_singleton_self _)

/-- The integral functional `x ↦ x₀ + i x₁` on `ℤ²`. -/
def b3A_ψ0 : (Fin 2 → ℤ) →ₗ[ℤ] ℂ where
  toFun x := (x 0 : ℂ) + Complex.I * (x 1 : ℂ)
  map_add' x y := by simp only [Pi.add_apply, Int.cast_add]; ring
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast]
    push_cast
    ring

/-- **The coordinate `z` of the elliptic curve**, `[c ⊗ x] ↦ c (x₀ + i x₁)` on `(ℂ ⊗ ℤ²) ⧸ F`. -/
def b3A_φ : ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) →ₗ[ℂ] ℂ :=
  b2_stdF.liftQ (LinearMap.liftBaseChange ℂ b3A_ψ0) (by
    rw [b2_stdF, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    simp [LinearMap.liftBaseChange_tmul, b3A_ψ0])

/-- The coordinate on classes of pure tensors. -/
theorem b3A_φ_mk (c : ℂ) (x : Fin 2 → ℤ) :
    b3A_φ (Submodule.Quotient.mk (c ⊗ₜ[ℤ] x)) = c * ((x 0 : ℂ) + Complex.I * (x 1 : ℂ)) := by
  simp [b3A_φ, LinearMap.liftBaseChange_tmul, b3A_ψ0]

/-- The coordinate of a lattice point `x` is `x₀ + i x₁`. -/
theorem b3A_φ_latticeMap (x : Fin 2 → ℤ) :
    b3A_φ (b2_latticeMap _ b2_stdF x) = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := by
  rw [show b2_latticeMap _ b2_stdF x = Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] x) from rfl,
    b3A_φ_mk, one_mul]

/-- `z([e₀]) = 1`. -/
theorem b3A_φ_e0 : b3A_φ (b3A_e 0) = 1 := by
  simp [b3A_e, b3A_φ_latticeMap]

/-- `z([e₁]) = i`. -/
theorem b3A_φ_e1 : b3A_φ (b3A_e 1) = Complex.I := by
  simp [b3A_e, b3A_φ_latticeMap]

/-- `[e₀] ≠ 0`. -/
theorem b3A_e0_ne_zero : b3A_e 0 ≠ 0 := fun h ↦ by
  simpa [h] using b3A_φ_e0

/-- The point with lattice coordinates `(s, t)` is `[s [e₀] + t [e₁]]`. -/
theorem b3A_ellipticPoint_eq (s t : ℝ) :
    b3_ellipticPoint s t = QuotientAddGroup.mk ((s : ℂ) • b3A_e 0 + (t : ℂ) • b3A_e 1) := by
  rw [b3_ellipticPoint]
  congr 1
  rw [Submodule.Quotient.mk_add]
  congr 1
  · rw [show ((s : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ)) =
        (s : ℂ) • ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], Submodule.Quotient.mk_smul]
    rfl
  · rw [show ((t : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ)) =
        (t : ℂ) • ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], Submodule.Quotient.mk_smul]
    rfl

/-- The elliptic curve is connected (statement 27). -/
instance b3A_elliptic_connected : ConnectedSpace b3_Elliptic := b3A_elliptic_connectedSpace

/-- The loop `a` is the straight line in direction `[e₀]`. -/
theorem b3A_ellipticA_eq : b3_ellipticA =
    fun u : ℝ ↦ (QuotientAddGroup.mk ((u : ℂ) • b3A_e 0 + 0) : b3_Elliptic) := by
  funext u
  simp [b3_ellipticA, b3A_ellipticPoint_eq]

/-- The loop `b` is the straight line in direction `[e₁]`. -/
theorem b3A_ellipticB_eq : b3_ellipticB =
    fun u : ℝ ↦ (QuotientAddGroup.mk ((u : ℂ) • b3A_e 1 + 0) : b3_Elliptic) := by
  funext u
  simp [b3_ellipticB, b3A_ellipticPoint_eq]

/-- The loop `a` is `C¹`. -/
theorem b3A_ellipticA_contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1 b3_ellipticA := by
  rw [b3A_ellipticA_eq]
  exact (b3A_torusLine b2_stdF (b3A_e 0) 0).1

/-- The loop `b` is `C¹`. -/
theorem b3A_ellipticB_contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1 b3_ellipticB := by
  rw [b3A_ellipticB_eq]
  exact (b3A_torusLine b2_stdF (b3A_e 1) 0).1

/-- `(ℂ ⊗ ℤ²) ⧸ F` is a complex line. -/
theorem b3A_finrank_quot : Module.finrank ℂ ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) = 1 := by
  have := b3_ellipticModel_finrank
  simpa using this

/-- `dim Ω¹ = 1` on the elliptic curve. -/
theorem b3A_elliptic_finrank_holForm :
    Module.finrank ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) = 1 :=
  (b3A_torus_finrank_holForm b2_stdF).trans b3A_finrank_quot

/-- The integral of a holomorphic form along a straight line of the torus. -/
theorem b3A_line_pathPeriod {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) [DiscreteTopology (b2_latticeMap Λ F).range]
    [IsManifold 𝓘(ℂ, b3A_TM F) ω (b2_torus Λ F)] [CompactSpace (b2_torus Λ F)]
    [ConnectedSpace (b2_torus Λ F)] (w c : (ℂ ⊗[ℤ] Λ) ⧸ F)
    (θ : b3_HolForm (b3A_TM F) (b2_torus Λ F)) :
    b3_pathPeriod (b3A_TM F) (b2_torus Λ F)
        (fun u : ℝ ↦ (QuotientAddGroup.mk ((u : ℂ) • w + c) : b2_torus Λ F)) θ =
      b3A_formFunctional F θ (b2_coord _ w) := by
  simp only [b3_pathPeriod, b3_pathIntegral]
  rw [b3A_torus_form_eq F θ]
  simp only [b3A_invForm, (b3A_torusLine F w c).2, intervalIntegral.integral_const, sub_zero,
    one_smul]
  rfl

/-- The form `dz`. -/
def b3A_dz : b3_HolForm b3_EllipticModel b3_Elliptic :=
  ⟨b3A_invForm b2_stdF (LinearMap.toContinuousLinearMap
      (b3A_φ ∘ₗ (b2_coord ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF)).symm.toLinearMap)),
    b3A_invForm_mem _ _⟩

/-- The functional of `dz` is the coordinate `z`. -/
theorem b3A_formFunctional_dz (w : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) :
    b3A_formFunctional b2_stdF b3A_dz (b2_coord _ w) = b3A_φ w := by
  simp [b3A_formFunctional, b3A_dz, b3A_invForm]

/-- The periods of `dz` on `a` and `b` are `1` and `i`. -/
theorem b3A_elliptic_periods (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic,
      b3_period _ _ a θ = 1 ∧ b3_period _ _ b θ = Complex.I := by
  refine ⟨b3A_dz, ?_, ?_⟩
  · rw [b3_period, ha, b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e0]
  · rw [b3_period, hb, b3A_ellipticB_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e1]

/-- The orientation of `(v, i v)` is positive for `v ≠ 0`. -/
theorem b3A_orient_I {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (v : E) (hv : v ≠ 0) : 0 < b3_orient E v (Complex.I • v) := by
  unfold b3_orient
  have hterm : ∀ i, (starRingEnd ℂ ((Module.finBasis ℂ E).equivFun v i) *
      (Module.finBasis ℂ E).equivFun (Complex.I • v) i).im =
        Complex.normSq ((Module.finBasis ℂ E).equivFun v i) := by
    intro i
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.normSq_apply]
    ring
  simp only [hterm]
  obtain ⟨i, hi⟩ : ∃ i, (Module.finBasis ℂ E).equivFun v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.finBasis ℂ E).equivFun.injective (by ext i; simp [h i]))
  exact Finset.sum_pos' (fun j _ ↦ Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

/-- The velocity of `a` is `[e₀]`. -/
theorem b3A_velocity_ellipticA (t : ℝ) :
    b3_velocity b3_EllipticModel b3_Elliptic b3_ellipticA t = b2_coord _ (b3A_e 0) := by
  rw [b3A_ellipticA_eq]
  exact (b3A_torusLine b2_stdF (b3A_e 0) 0).2 t

/-- The velocity of `b` is `i [e₀]`. -/
theorem b3A_velocity_ellipticB (t : ℝ) :
    b3_velocity b3_EllipticModel b3_Elliptic b3_ellipticB t =
      Complex.I • b2_coord _ (b3A_e 0) := by
  rw [b3A_ellipticB_eq, (b3A_torusLine b2_stdF (b3A_e 1) 0).2 t, b3A_e_one, map_smul]

/-- The velocities of `a` and `b` are positively oriented. -/
theorem b3A_orient_ab (s t : ℝ) :
    0 < b3_orient b3_EllipticModel (b3_velocity b3_EllipticModel b3_Elliptic b3_ellipticA s)
      (b3_velocity b3_EllipticModel b3_Elliptic b3_ellipticB t) := by
  rw [b3A_velocity_ellipticA, b3A_velocity_ellipticB]
  refine b3A_orient_I _ ?_
  intro h
  exact b3A_e0_ne_zero ((b2_coord _).injective (h.trans (map_zero _).symm))

/-- The loops `a` and `b` are transverse. -/
theorem b3A_elliptic_transverse (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_Transverse b3_EllipticModel a b := by
  intro s t _
  rw [ha, hb]
  exact (b3A_orient_ab s t).ne'

/-- The loops `a` and `b` meet only where both parameters are integers. -/
theorem b3A_ellipticA_eq_B {s t : ℝ} (h : b3_ellipticA s = b3_ellipticB t) :
    ∃ m n : ℤ, (m : ℝ) = s ∧ (n : ℝ) = t := by
  rw [b3A_ellipticA_eq, b3A_ellipticB_eq] at h
  simp only [add_zero] at h
  obtain ⟨x, hx⟩ := (QuotientAddGroup.eq).1 h
  have := congrArg b3A_φ hx
  rw [b3A_φ_latticeMap, map_add, map_neg, map_smul, map_smul, b3A_φ_e0, b3A_φ_e1,
    smul_eq_mul, smul_eq_mul, mul_one] at this
  refine ⟨-x 0, x 1, ?_, ?_⟩
  · have h1 := congrArg Complex.re this
    simp at h1
    push_cast
    linarith
  · have h1 := congrArg Complex.im this
    simp at h1
    exact h1

/-- The only crossing of `a` and `b` in `[0, 1)²` is `(0, 0)`. -/
theorem b3A_crossings_ab (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_crossings b3_EllipticModel a b = {((0 : ℝ), (0 : ℝ))} := by
  ext ⟨s, t⟩
  simp only [b3_crossings, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq, ha, hb]
  constructor
  · rintro ⟨hs, ht, h⟩
    obtain ⟨m, n, rfl, rfl⟩ := b3A_ellipticA_eq_B h
    have hm : m = 0 := by
      have h1 : (0 : ℝ) ≤ m := hs.1
      have h2 : (m : ℝ) < 1 := hs.2
      have : (0 : ℤ) ≤ m := by exact_mod_cast h1
      have : m < 1 := by exact_mod_cast h2
      omega
    have hn : n = 0 := by
      have h1 : (0 : ℝ) ≤ n := ht.1
      have h2 : (n : ℝ) < 1 := ht.2
      have : (0 : ℤ) ≤ n := by exact_mod_cast h1
      have : n < 1 := by exact_mod_cast h2
      omega
    simp [hm, hn]
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨le_rfl, one_pos⟩, ⟨le_rfl, one_pos⟩, ?_⟩
    simp [b3_ellipticA, b3_ellipticB]

/-- `a · b = 1`. -/
theorem b3A_elliptic_intersection (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_intersection b3_EllipticModel a b = 1 := by
  rw [b3_intersection, b3A_crossings_ab a b ha hb, finsum_mem_singleton, ha, hb,
    sign_pos (b3A_orient_ab 0 0)]
  rfl

/-- An Abel–Jacobi map based at `0` sends `[s e₀ + t e₁]` to `[s ⊗ λ_a + t ⊗ λ_b]`: along the
segment from `0` every holomorphic form `θ` integrates to `s ∫_a θ + t ∫_b θ`. -/
theorem b3A_elliptic_abelJacobi_apply (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) (s t : ℝ) :
    aj (b3_ellipticPoint s t) = QuotientAddGroup.mk (Submodule.Quotient.mk
      ((s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ a + (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b)) := by
  suffices key : ∀ w : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF,
      w = (s : ℂ) • b3A_e 0 + (t : ℂ) • b3A_e 1 →
      aj (b3_ellipticPoint s t) = QuotientAddGroup.mk (Submodule.Quotient.mk
        ((s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ a + (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b)) from
    key _ rfl
  intro w hw
  have hl : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1
      (fun u : ℝ ↦ (QuotientAddGroup.mk ((u : ℂ) • w + 0) : b3_Elliptic)) :=
    (b3A_torusLine b2_stdF w 0).1
  have h3 := h.2 (fun u : ℝ ↦ (QuotientAddGroup.mk ((u : ℂ) • w + 0) : b3_Elliptic))
  have h4 := h3 hl
  obtain ⟨v, hvv⟩ := h4
  have hv := hvv.1
  have hv' := hvv.2
  have h1 : (QuotientAddGroup.mk (((1 : ℝ) : ℂ) • w + 0) : b3_Elliptic) =
      b3_ellipticPoint s t := by
    rw [b3A_ellipticPoint_eq, ← hw, Complex.ofReal_one, one_smul, add_zero]
  have h0 : (QuotientAddGroup.mk (((0 : ℝ) : ℂ) • w + 0) : b3_Elliptic) = 0 := by
    rw [Complex.ofReal_zero, zero_smul, add_zero, QuotientAddGroup.mk_zero]
  simp only [h1, h0, h.1, sub_zero] at hv'
  refine hv'.trans (congrArg
    (fun z ↦ (QuotientAddGroup.mk z : b3_Jacobian b3_EllipticModel b3_Elliptic)) ?_)
  refine (Submodule.Quotient.eq (b3_periodF b3_EllipticModel b3_Elliptic)).2 ?_
  change _ ∈ LinearMap.ker (b3_cplxPeriod _ _)
  refine LinearMap.sub_mem_ker_iff.2 (hv.trans ?_)
  rw [map_add]
  funext θ
  simp only [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  change b3_pathPeriod _ _ _ θ = (s : ℂ) * b3_pathPeriod _ _ a.1 θ +
    (t : ℂ) * b3_pathPeriod _ _ b.1 θ
  rw [ha, hb, b3A_ellipticA_eq, b3A_ellipticB_eq, b3A_line_pathPeriod, b3A_line_pathPeriod,
    b3A_line_pathPeriod, hw]
  simp only [map_add, map_smul, smul_eq_mul]

end Elliptic

end HodgeLean.Foundations.Program

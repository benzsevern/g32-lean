import HodgeLean.Foundations.Program.HurwitzPrymCovLocal

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: rotation generators of stabilizers

For a finite group acting faithfully by holomorphic automorphisms on a connected Riemann surface,
the derivative at a fixed point `x` is a character `λ_x : G_x → ℂˣ`. It is injective (Cartan's
averaging: an element with derivative `1` is the identity near `x`, hence everywhere by the
identity theorem, hence trivial by faithfulness), so `G_x` is cyclic and `e^{2πi/|G_x|}` is the
derivative of exactly one element.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Rot

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [MulAction G C]

/-- The derivative of `z ↦ h • z` at `x`, as an endomorphism of the model line. -/
def b4cov_der (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E C]
    (x : C) (h : G) : E →L[ℂ] E :=
  mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun z : C ↦ h • z) x

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b4cov_der_one (x : C) : b4cov_der E (G := G) x 1 = ContinuousLinearMap.id ℂ E := by
  have : (fun z : C ↦ (1 : G) • z) = id := funext fun z ↦ one_smul G z
  rw [b4cov_der, this, mfderiv_id]
  rfl

theorem b4cov_der_mul (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (x : C) (g h : G) (hx : h • x = x) :
    b4cov_der E x (g * h) = (b4cov_der E x g).comp (b4cov_der E x h) := by
  have hcomp : (fun z : C ↦ (g * h) • z) = (fun z : C ↦ g • z) ∘ (fun z : C ↦ h • z) :=
    funext fun z ↦ mul_smul g h z
  have hg' : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun z : C ↦ g • z) (h • x) :=
    ((hG g) (h • x)).mdifferentiableAt (by simp)
  have hh' : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun z : C ↦ h • z) x :=
    ((hG h) x).mdifferentiableAt (by simp)
  have hpt : (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun z : C ↦ g • z) (h • x) : E →L[ℂ] E) =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun z : C ↦ g • z) x := by
    rw [hx]
  rw [b4cov_der, hcomp, mfderiv_comp x hg' hh']
  exact congrArg (fun L : E →L[ℂ] E ↦ L.comp (b4cov_der E x h)) hpt

section Scalar

variable (hE : Module.finrank ℂ E = 1)
include hE

/-- A fixed identification of the model line with `ℂ`. -/
def b4cov_lineEquiv : ℂ ≃L[ℂ] E :=
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  ContinuousLinearEquiv.ofFinrankEq (by rw [hE, Module.finrank_self])

/-- An endomorphism of a complex line is a scalar. -/
theorem b4cov_eq_smul (T : E →L[ℂ] E) (v : E) :
    T v = (b4cov_lineEquiv hE).symm (T (b4cov_lineEquiv hE 1)) • v := by
  set L := b4cov_lineEquiv hE
  have hv : v = L.symm v • L 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  have hT : T (L 1) = L.symm (T (L 1)) • L 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, ContinuousLinearEquiv.apply_symm_apply]
  conv_lhs => rw [hv, map_smul, hT, smul_smul, mul_comm, ← smul_smul, ← hv]

theorem b4cov_lineEquiv_one_ne_zero : b4cov_lineEquiv hE 1 ≠ 0 := by
  rw [map_ne_zero_iff _ (b4cov_lineEquiv hE).injective]
  exact one_ne_zero

/-- The scalar of the derivative at `x`. -/
def b4cov_lam (x : C) (h : G) : ℂ :=
  (b4cov_lineEquiv hE).symm (b4cov_der E x h (b4cov_lineEquiv hE 1))

theorem b4cov_der_apply (x : C) (h : G) (v : E) : b4cov_der E x h v = b4cov_lam hE x h • v :=
  b4cov_eq_smul hE _ v

/-- The scalar is determined by the action on any nonzero vector. -/
theorem b4cov_lam_eq_of_apply (x : C) (h : G) (c : ℂ) (hc : ∀ v : E, b4cov_der E x h v = c • v) :
    b4cov_lam hE x h = c := by
  have h1 := hc (b4cov_lineEquiv hE 1)
  rw [b4cov_der_apply hE] at h1
  exact smul_left_injective ℂ (b4cov_lineEquiv_one_ne_zero hE) h1

theorem b4cov_lam_one (x : C) : b4cov_lam hE (G := G) x 1 = 1 :=
  b4cov_lam_eq_of_apply hE x 1 1 fun v ↦ by rw [b4cov_der_one, one_smul]; rfl

theorem b4cov_lam_mul (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (x : C) (g h : G) (hx : h • x = x) :
    b4cov_lam hE x (g * h) = b4cov_lam hE x g * b4cov_lam hE x h :=
  b4cov_lam_eq_of_apply hE x _ _ fun v ↦ by
    rw [b4cov_der_mul hG x g h hx, ContinuousLinearMap.comp_apply, b4cov_der_apply hE,
      b4cov_der_apply hE, smul_smul]

/-- **The derivative character** of the stabilizer of `x`. -/
def b4cov_lamHom (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (x : C) :
    MulAction.stabilizer G x →* ℂ where
  toFun h := b4cov_lam hE x (h : G)
  map_one' := b4cov_lam_one hE x
  map_mul' g h := b4cov_lam_mul hE hG x g h h.2

end Scalar

/-- **Cartan's lemma**: an element of a finite group of holomorphic automorphisms of a connected
surface acting faithfully, fixing `x` with derivative `1` there, is trivial. -/
theorem b4cov_eq_one_of_lam [Finite G] [T2Space C] [ConnectedSpace C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (x : C) (k : G) (hk : k • x = x) (hl : b4cov_lam hE x k = 1) : k = 1 := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have := FiniteDimensional.complete ℂ E
  have hpow : ∀ j : ℕ, k ^ j • x = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hk, ih]
  have hlj : ∀ j : ℕ, b4cov_lam hE x (k ^ j) = 1 := by
    intro j
    induction j with
    | zero => simpa using b4cov_lam_one hE (G := G) x
    | succ j ih => rw [pow_succ, b4cov_lam_mul hE hG x _ _ hk, ih, hl, one_mul]
  have hderj : ∀ j : ℕ, b4cov_der E x (k ^ j) = ContinuousLinearMap.id ℂ E := by
    intro j
    ext v
    rw [b4cov_der_apply hE, hlj, one_smul]
    rfl
  have hm : 0 < orderOf k := orderOf_pos k
  set m := orderOf k
  set φ := extChartAt 𝓘(ℂ, E) x
  let ψ : C → E := fun y ↦ (m : ℂ)⁻¹ • ∑ j ∈ Finset.range m, φ (k ^ j • y)
  have hψk : ∀ y, ψ (k • y) = ψ y := by
    intro y
    simp only [ψ]
    congr 1
    have hs : ∀ j, k ^ j • k • y = k ^ (j + 1) • y := fun j ↦ by rw [← mul_smul, ← pow_succ]
    simp only [hs]
    have h1 := Finset.sum_range_succ (fun j ↦ φ (k ^ j • y)) m
    have h2 := Finset.sum_range_succ' (fun j ↦ φ (k ^ j • y)) m
    rw [pow_orderOf_eq_one, one_smul] at h1
    simp only [pow_zero, one_smul] at h2
    exact add_right_cancel (h2.symm.trans h1)
  let Ψ : E → E := ψ ∘ φ.symm
  have hGj : ∀ j : ℕ, HasStrictFDerivAt (fun z ↦ φ (k ^ j • φ.symm z))
      (ContinuousLinearMap.id ℂ E) (φ x) := by
    intro j
    have han := b4cov_analyticAt_chart (fun y : C ↦ k ^ j • y) (hG _) x x (φ x)
      (mem_extChartAt_target x) (by
        simp only [φ, extChartAt_to_inv, hpow]
        exact mem_extChartAt_source x)
    have hmd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : C ↦ k ^ j • y) x :=
      ((hG _) x).mdifferentiableAt (by simp)
    have hab := hmd.mfderiv_abuse
    rw [modelWithCornersSelf_coe, range_id, fderivWithin_univ] at hab
    have hw : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E) x (fun y : C ↦ k ^ j • y) =
        extChartAt 𝓘(ℂ, E) x ∘ (fun y : C ↦ k ^ j • y) ∘ (extChartAt 𝓘(ℂ, E) x).symm := by
      simp only [writtenInExtChartAt, hpow]
    rw [hw] at hab
    have hd : fderiv ℂ (extChartAt 𝓘(ℂ, E) x ∘ (fun y : C ↦ k ^ j • y) ∘
        (extChartAt 𝓘(ℂ, E) x).symm) (φ x) = ContinuousLinearMap.id ℂ E := by
      rw [← hab]
      exact hderj j
    have := han.hasStrictFDerivAt
    rw [hd] at this
    exact this
  have hΨ : HasStrictFDerivAt Ψ (ContinuousLinearMap.id ℂ E) (φ x) := by
    have hsum := HasStrictFDerivAt.sum (u := Finset.range m) fun j _ ↦ hGj j
    have := hsum.const_smul ((m : ℂ)⁻¹)
    convert this using 1
    · funext z
      simp only [Ψ, ψ, Function.comp_apply, Pi.smul_apply, Finset.sum_apply]
    · rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm.ne'), one_smul]
  have hΨ' : HasStrictFDerivAt Ψ ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E)
      (φ x) := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hΨ
  let P := hΨ'.toOpenPartialHomeomorph Ψ
  have hP : (P : E → E) = Ψ := hΨ'.toOpenPartialHomeomorph_coe
  have hsrc : P.source ∈ 𝓝 (φ x) :=
    P.open_source.mem_nhds hΨ'.mem_toOpenPartialHomeomorph_source
  have hcont : ContinuousAt (fun y ↦ φ (k • y)) x := by
    have h1 : ContinuousAt φ (k • x) := by rw [hk]; exact continuousAt_extChartAt x
    exact h1.comp (hG k).continuous.continuousAt
  have hloc : ∀ᶠ y in 𝓝 x, k • y = y := by
    have h1 : ∀ᶠ y in 𝓝 x, φ y ∈ P.source := (continuousAt_extChartAt x).preimage_mem_nhds hsrc
    have h2 : ∀ᶠ y in 𝓝 x, φ (k • y) ∈ P.source :=
      hcont.preimage_mem_nhds (by simp only [hk]; exact hsrc)
    have h3 : ∀ᶠ y in 𝓝 x, y ∈ φ.source := extChartAt_source_mem_nhds x
    have h4 : ∀ᶠ y in 𝓝 x, k • y ∈ φ.source :=
      (hG k).continuous.continuousAt.preimage_mem_nhds (by rw [hk]; exact extChartAt_source_mem_nhds x)
    filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
    have heq : Ψ (φ (k • y)) = Ψ (φ y) := by
      simp only [Ψ, Function.comp_apply, φ.left_inv hy3, φ.left_inv hy4, hψk]
    have := P.injOn hy2 hy1 (by rw [hP]; exact heq)
    exact φ.injOn hy4 hy3 this
  have hall := b4cov_eq_of_eventuallyEq (fun y : C ↦ k • y) id (hG k) contMDiff_id x hloc
  exact eq_of_smul_eq_smul fun y ↦ by rw [one_smul]; exact congrFun hall y

section Exists

variable [Finite G] [T2Space C] [ConnectedSpace C] [FaithfulSMul G C]
  (hE : Module.finrank ℂ E = 1)
  (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
include hE hG

/-- **The derivative character is injective.** -/
theorem b4cov_lamHom_injective (x : C) : Function.Injective (b4cov_lamHom hE hG x) := by
  intro a b hab
  have h1 : b4cov_lamHom hE hG x (a * b⁻¹) = 1 := by
    rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
  have h2 := b4cov_eq_one_of_lam hE hG x ((a * b⁻¹ : MulAction.stabilizer G x) : G)
    (a * b⁻¹).2 h1
  have : a * b⁻¹ = 1 := Subtype.ext h2
  exact mul_inv_eq_one.1 this

/-- **Each stabilizer has a rotation generator.** -/
theorem b4cov_exists_rotGen (x : C) : ∃ h : G, b4_IsRotGen E x h := by
  classical
  have : Fintype (MulAction.stabilizer G x) := Fintype.ofFinite _
  set n := Nat.card (MulAction.stabilizer G x)
  have hn : 0 < n := Nat.card_pos
  set χ := b4cov_lamHom hE hG x
  have hinj := b4cov_lamHom_injective hE hG x
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hsub : Finset.univ.image χ ⊆ Polynomial.nthRootsFinset n (1 : ℂ) := by
    intro c hc
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hc
    rw [Polynomial.mem_nthRootsFinset hn, ← map_pow, pow_card_eq_one', map_one]
  have hcard : (Polynomial.nthRootsFinset n (1 : ℂ)).card ≤ (Finset.univ.image χ).card := by
    rw [hζ.card_nthRootsFinset, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    exact le_of_eq Nat.card_eq_fintype_card
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : ζ ∈ Finset.univ.image χ := by
    rw [heq, Polynomial.mem_nthRootsFinset hn]
    exact hζ.pow_eq_one
  obtain ⟨h, -, hh⟩ := Finset.mem_image.1 hmem
  have hord : orderOf (h : G) = n := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective χ hinj h, hh]
    exact hζ.eq_orderOf.symm
  refine ⟨h, h.2, hord, fun v ↦ ?_⟩
  rw [hord]
  have hl : b4cov_lam hE x (h : G) = ζ := hh
  change b4cov_der E x h v = _
  rw [b4cov_der_apply hE]
  exact congrArg (· • v) hl

/-- **The rotation generator is unique.** -/
theorem b4cov_rotGen_unique (x : C) (h h' : G) (hh : b4_IsRotGen E x h)
    (hh' : b4_IsRotGen E x h') : h = h' := by
  have e1 : b4cov_lam hE x h = Complex.exp (2 * Real.pi * Complex.I /
      (Nat.card (MulAction.stabilizer G x) : ℂ)) := by
    rw [← hh.2.1]; exact b4cov_lam_eq_of_apply hE x h _ hh.2.2
  have e2 : b4cov_lam hE x h' = Complex.exp (2 * Real.pi * Complex.I /
      (Nat.card (MulAction.stabilizer G x) : ℂ)) := by
    rw [← hh'.2.1]; exact b4cov_lam_eq_of_apply hE x h' _ hh'.2.2
  have := b4cov_lamHom_injective hE hG x (a₁ := ⟨h, hh.1⟩) (a₂ := ⟨h', hh'.1⟩)
    (e1.trans e2.symm)
  exact congrArg Subtype.val this

end Exists

end Rot

end HodgeLean.Foundations.Program

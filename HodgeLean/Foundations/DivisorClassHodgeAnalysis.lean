import HodgeLean.Foundations.DivisorClassHodgeDefs
import HodgeLean.Foundations.SeveralVariableDbar
import HodgeLean.Foundations.AutomorphyChernClass
import HodgeConjecture.Mathlib.Analysis.Calculus.DifferentialForm.Poincare

/-! # Divisor classes on abelian varieties: analysis on `ℂ^n` (DC1, sub-stages a, b)

Helpers for the bodies `dc1_periodic_entire_const_aux`, `dc1_smooth_coboundary_aux`,
`dc1_holomorphic_poincare_aux` and `dc1_typeOneOne_of_affine_aux`:

* `dca_periodic_entire_const`: Liouville for lattice-periodic entire functions, which are
  bounded by their values on the bounded fundamental domain `ZSpan.fundamentalDomain`;
* `dca_smooth_coboundary`: a smooth partition of unity `ρ` subordinate to the lattice
  translates of a `ContDiffBump` (a locally finite `finsum`), and the coboundary
  `φ(z) = -∑_l ρ(z + l) a_l(z)`;
* `dca_holomorphic_poincare`: the radial primitive `h(z) = ∫₀¹ ∑_j u_j(t z) z_j dt`,
  differentiated under the integral sign;
* `dca_typeOneOne_of_affine`: the real-linear extension of `lin` along a lattice basis and the
  identity `B(iv, iw) = B(v, w) + i (B(v, iw) + B(iv, w))`.

HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Foundations.AppellHumbert
open Filter Set Topology
open scoped ContDiff

namespace HodgeLean.Foundations

section Poincare

variable {n : ℕ}

theorem dca_contDiff {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) {m : WithTop ℕ∞} :
    ContDiff ℂ m f := by
  rw [← contDiffOn_univ]
  exact (AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn_fin isOpen_univ
    hf.differentiableOn).contDiffOn uniqueDiffOn_univ

theorem dca_continuous_fderiv {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    Continuous (fderiv ℂ f) :=
  (dca_contDiff hf (m := 1)).continuous_fderiv (by simp)

theorem dca_sum_single_apply (D : (Fin n → ℂ) →L[ℂ] ℂ) (z : Fin n → ℂ) :
    ∑ j, z j * D (Pi.single j 1) = D z := by
  conv_rhs => rw [← Finset.univ_sum_single z]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show (Pi.single j (z j) : Fin n → ℂ) = z j • Pi.single j 1 by
    rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem dca_holomorphic_poincare (u : Fin n → (Fin n → ℂ) → ℂ)
    (hu : ∀ j, Differentiable ℂ (u j))
    (hclosed : ∀ j k z, fderiv ℂ (u j) z (Pi.single k 1) = fderiv ℂ (u k) z (Pi.single j 1)) :
    ∃ h : (Fin n → ℂ) → ℂ, Differentiable ℂ h ∧
      ∀ j z, fderiv ℂ h z (Pi.single j 1) = u j z := by
  let F : (Fin n → ℂ) → ℝ → ℂ := fun z t ↦ ∑ j, u j ((t : ℂ) • z) * z j
  let F' : (Fin n → ℂ) → ℝ → (Fin n → ℂ) →L[ℂ] ℂ := fun z t ↦
    ∑ j, (u j ((t : ℂ) • z) • ContinuousLinearMap.proj j +
      z j • (fderiv ℂ (u j) ((t : ℂ) • z)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ _))
  have hc : ∀ j, Continuous (u j) := fun j ↦ (hu j).continuous
  have hc' : ∀ j, Continuous (fderiv ℂ (u j)) := fun j ↦ dca_continuous_fderiv (hu j)
  have hFc : Continuous fun p : (Fin n → ℂ) × ℝ ↦ F p.1 p.2 := by
    simp only [F]; fun_prop
  have hF'c : Continuous fun p : (Fin n → ℂ) × ℝ ↦ F' p.1 p.2 := by
    simp only [F']; fun_prop
  have hdiff : ∀ z t, HasFDerivAt (F · t) (F' z t) z := by
    intro z t
    simp only [F, F']
    refine HasFDerivAt.fun_sum fun j _ ↦ ?_
    have h1 : HasFDerivAt (fun x : Fin n → ℂ ↦ u j ((t : ℂ) • x))
        ((fderiv ℂ (u j) ((t : ℂ) • z)).comp ((t : ℂ) • ContinuousLinearMap.id ℂ _)) z :=
      (hu j _).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul (t : ℂ))
    exact h1.mul (hasFDerivAt_apply j z)
  refine ⟨fun z ↦ ∫ t in (0 : ℝ)..1, F z t, fun z ↦
    (DifferentialForm.hasFDerivAt_intervalIntegral_of_continuous F F' z hFc hF'c hdiff
      ).differentiableAt, fun k z ↦ ?_⟩
  rw [(DifferentialForm.hasFDerivAt_intervalIntegral_of_continuous F F' z hFc hF'c
    hdiff).fderiv]
  have hint : IntervalIntegrable (F' z) MeasureTheory.volume 0 1 :=
    (hF'c.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  let G : ℝ → ℂ := fun t ↦ (t : ℂ) * u k ((t : ℂ) • z)
  let G' : ℝ → ℂ := fun t ↦ u k ((t : ℂ) • z) + (t : ℂ) * fderiv ℂ (u k) ((t : ℂ) • z) z
  have hG : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℂ ↦ s * u k (s • z))
        (1 * u k ((t : ℂ) • z) + (t : ℂ) * fderiv ℂ (u k) ((t : ℂ) • z) z) (t : ℂ) := by
      refine (hasDerivAt_id (t : ℂ)).mul ?_
      have := (hu k _).hasFDerivAt.comp_hasDerivAt (t : ℂ) ((hasDerivAt_id (t : ℂ)).smul_const z)
      convert this using 1
      · rfl
      · simp
    simpa [G, G'] using h0.comp_ofReal
  have hpt : ∀ t, F' z t (Pi.single k 1) = G' t := by
    intro t
    simp only [F', G', FunLike.coe_sum, Finset.sum_apply, add_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      map_smul, Finset.sum_add_distrib]
    rw [← dca_sum_single_apply (fderiv ℂ (u k) ((t : ℂ) • z)) z, Finset.mul_sum]
    have e1 : ∑ c, u c ((t : ℂ) • z) * (Pi.single k (1 : ℂ) : Fin n → ℂ) c = u k ((t : ℂ) • z) := by
      simp [Pi.single_apply]
    rw [e1]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hclosed j k]; ring
  simp_rw [hpt]
  have hG'c : Continuous G' := by
    simp only [G']
    have := hc' k
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hG t)
    (hG'c.intervalIntegrable 0 1)]
  simp [G]

end Poincare

section Lattice

variable {n : ℕ} (L : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The real basis of `Fin n → ℂ` given by the chosen `ℤ`-basis of a full lattice.
Source: Mathlib `Module.Basis.ofZLatticeBasis`; Birkenhake–Lange, *Complex Abelian Varieties*,
2nd ed., §1.1 (a lattice basis is a real basis). -/
abbrev dca_basis : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ (Fin n → ℂ) :=
  (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

example (i : Module.Free.ChooseBasisIndex ℤ L) :
    dca_basis L i = Module.Free.chooseBasis ℤ L i :=
  Module.Basis.ofZLatticeBasis_apply ℝ L _ i

theorem dca_floor_mem (z : Fin n → ℂ) : (ZSpan.floor (dca_basis L) z : Fin n → ℂ) ∈ L := by
  exact ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ).le (ZSpan.floor (dca_basis L) z).2

theorem dca_eq_fract_add (z : Fin n → ℂ) :
    z = ZSpan.fract (dca_basis L) z + (ZSpan.floor (dca_basis L) z : Fin n → ℂ) := by
  rw [ZSpan.fract_apply]; abel

theorem dca_range_subset {α : Type*} (h : (Fin n → ℂ) → α) (hper : ∀ (l : L) z, h (z + l) = h z) :
    range h ⊆ h '' ZSpan.fundamentalDomain (dca_basis L) := by
  rintro _ ⟨z, rfl⟩
  refine ⟨_, ZSpan.fract_mem_fundamentalDomain _ z, ?_⟩
  have := hper ⟨_, dca_floor_mem L z⟩ (ZSpan.fract (dca_basis L) z)
  simp only at this
  calc h (ZSpan.fract (dca_basis L) z) = _ := this.symm
    _ = h z := by rw [← dca_eq_fract_add]

theorem dca_periodic_isBounded (h : (Fin n → ℂ) → ℂ) (hh : Continuous h)
    (hper : ∀ (l : L) z, h (z + l) = h z) : Bornology.IsBounded (range h) := by
  have hK : IsCompact (closure (ZSpan.fundamentalDomain (dca_basis L))) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  exact ((hK.image hh).isBounded).subset
    ((dca_range_subset L h hper).trans (image_mono subset_closure))

theorem dca_periodic_entire_const (h : (Fin n → ℂ) → ℂ) (hh : Differentiable ℂ h)
    (hper : ∀ (l : L) z, h (z + l) = h z) (z w : Fin n → ℂ) : h z = h w :=
  hh.apply_eq_apply_of_bounded (dca_periodic_isBounded L h hh.continuous hper) z w

theorem dca_typeOneOne_of_affine (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, (B l m : ℂ) = lin m l - lin l m) :
    IsTypeOneOne (fun v w ↦ B v w) := by
  set bL := Module.Free.chooseBasis ℤ L
  set b := dca_basis L
  let g : Module.Free.ChooseBasisIndex ℤ L → (Fin n → ℂ) →ₗ[ℝ] ℂ :=
    fun i ↦ (lin (bL i)).restrictScalars ℝ
  let T : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℂ := b.constr ℝ g
  have hT : ∀ i v, T (b i) v = lin (bL i) v := fun i v ↦ by
    simp [T, g]
  have hTI : ∀ v w, T w (Complex.I • v) = Complex.I * T w v := by
    intro v w
    have : T.flip (Complex.I • v) = (LinearMap.mulLeft ℝ Complex.I).comp (T.flip v) := by
      refine b.ext fun i ↦ ?_
      simp only [LinearMap.flip_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, hT,
        map_smul, smul_eq_mul]
    simpa using LinearMap.congr_fun this w
  have hBT : ∀ v w, (B v w : ℂ) = T w v - T v w := by
    have : B.compr₂ (Complex.ofRealCLM.toLinearMap) = T.flip - T := by
      refine LinearMap.ext_basis b b fun i j ↦ ?_
      simp only [LinearMap.compr₂_apply, ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply,
        LinearMap.sub_apply, LinearMap.flip_apply, hT]
      have := hB (bL i) (bL j)
      simp only [b, Module.Basis.ofZLatticeBasis_apply] at this ⊢
      exact this
    intro v w
    simpa using LinearMap.congr_fun (LinearMap.congr_fun this v) w
  intro v w
  have h1 := hBT (Complex.I • v) (Complex.I • w)
  have h2 := hBT v (Complex.I • w)
  have h3 := hBT (Complex.I • v) w
  have h0 := hBT v w
  simp only [hTI] at h1 h2 h3
  have key : (B (Complex.I • v) (Complex.I • w) : ℂ) =
      B v w + Complex.I * (B v (Complex.I • w) + B (Complex.I • v) w) := by
    rw [h1, h0, h2, h3]
    linear_combination (T v w - T w v) * Complex.I_sq
  have := congrArg Complex.re key
  simpa using this

/-- Only finitely many lattice points lie in a ball. -/
theorem dca_finite_ball (c : Fin n → ℂ) (r : ℝ) : {l : L | ‖(l : Fin n → ℂ) - c‖ < r}.Finite := by
  have h := ZSpan.setFinite_inter (dca_basis L) (Metric.isBounded_ball (x := c) (r := r))
  rw [Module.Basis.ofZLatticeBasis_span] at h
  refine (h.preimage Subtype.val_injective.injOn).subset fun l hl ↦ ?_
  exact ⟨mem_ball_iff_norm.2 hl, l.2⟩

/-- A family indexed by the lattice whose `l`-th member is supported in the ball of radius `r`
about `-l` is locally finite. -/
theorem dca_locallyFinite {α : Type*} [Zero α] (r : ℝ) (g : L → (Fin n → ℂ) → α)
    (hg : ∀ l z, g l z ≠ 0 → ‖z + l‖ < r) : LocallyFinite fun l ↦ Function.support (g l) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  refine (dca_finite_ball L (-x) (r + 1)).subset ?_
  rintro l ⟨z, hz, hzx⟩
  have h1 := hg l z hz
  have h2 : ‖z - x‖ < 1 := mem_ball_iff_norm.1 hzx
  simp only [mem_ofPred_eq, sub_neg_eq_add]
  calc ‖(l : Fin n → ℂ) + x‖ = ‖(z + l) - (z - x)‖ := by congr 1; abel
    _ ≤ ‖z + l‖ + ‖z - x‖ := norm_sub_le _ _
    _ < r + 1 := add_lt_add h1 h2

theorem dca_contDiff_finsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (g : ι → (Fin n → ℂ) → F)
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hlf : LocallyFinite fun i ↦ Function.support (g i)) :
    ContDiff ℝ ∞ fun z ↦ ∑ᶠ i, g i z := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf x
  have : ContDiff ℝ ∞ fun y ↦ ∑ i ∈ s, g i y := ContDiff.sum fun i _ ↦ hg i
  exact this.contDiffAt.congr_of_eventuallyEq hs

theorem dca_finite_support {α : Type*} [Zero α] {ι : Type*} (g : ι → (Fin n → ℂ) → α)
    (hlf : LocallyFinite fun i ↦ Function.support (g i)) (z : Fin n → ℂ) :
    (Function.support fun i ↦ g i z).Finite :=
  hlf.point_finite z

theorem dca_smooth_coboundary (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, ContDiff ℝ ∞ (a l))
    (hcoc : ∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) :
    ∃ φ : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ φ ∧ ∀ (l : L) z, φ (z + l) - φ z = a l z := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
    (ZSpan.fundamentalDomain_isBounded (dca_basis L))
  let β : ContDiffBump (0 : Fin n → ℂ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hβsupp : ∀ (l : L) z, β (z + l) ≠ 0 → ‖z + l‖ < |R| + 2 := by
    intro l z h
    have : z + l ∈ Function.support β := h
    rw [β.support_eq] at this
    simpa using this
  have hlfβ := dca_locallyFinite L _ (fun (l : L) (z : Fin n → ℂ) ↦ β (z + l)) hβsupp
  let S : (Fin n → ℂ) → ℝ := fun z ↦ ∑ᶠ l : L, β (z + l)
  have hSc : ContDiff ℝ ∞ S :=
    dca_contDiff_finsum (fun (l : L) (z : Fin n → ℂ) ↦ β (z + l))
      (fun l ↦ β.contDiff.comp (contDiff_id.add contDiff_const)) hlfβ
  have hSper : ∀ (m : L) z, S (z + m) = S z := by
    intro m z
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.addRight m) (f := fun l : L ↦ β (z + l)))
    refine finsum_congr fun l ↦ ?_
    simp only [Equiv.coe_addRight, Submodule.coe_add]
    congr 1; abel
  have hS1 : ∀ z, 1 ≤ S z := by
    intro z
    let l₀ : L := -⟨_, dca_floor_mem L z⟩
    have hl₀ : β (z + l₀) = 1 := by
      apply β.one_of_mem_closedBall
      have : z + l₀ = ZSpan.fract (dca_basis L) z := by
        simp [l₀, ZSpan.fract_apply, sub_eq_add_neg]
      rw [this, mem_closedBall_zero_iff]
      have := hR _ (ZSpan.fract_mem_fundamentalDomain (dca_basis L) z)
      show _ ≤ |R| + 1
      linarith [le_abs_self R]
    rw [← hl₀]
    exact single_le_finsum l₀ (dca_finite_support _ hlfβ z) fun l ↦ β.nonneg
  have hS0 : ∀ z, S z ≠ 0 := fun z ↦ (lt_of_lt_of_le one_pos (hS1 z)).ne'
  let ρ : (Fin n → ℂ) → ℝ := fun z ↦ β z / S z
  have hρc : ContDiff ℝ ∞ ρ := β.contDiff.div hSc hS0
  have hρsum : ∀ z, ∑ᶠ l : L, ρ (z + l) = 1 := by
    intro z
    simp only [ρ, hSper, div_eq_mul_inv]
    rw [← finsum_mul]
    exact mul_inv_cancel₀ (hS0 z)
  have hρfin : ∀ z, (Function.support fun l : L ↦ ρ (z + l)).Finite := by
    intro z
    refine (dca_finite_support _ hlfβ z).subset fun l hl h0 ↦ hl ?_
    simp only [ρ] at h0 ⊢
    rw [h0, zero_div]
  have hρsumC : ∀ z, ∑ᶠ l : L, (ρ (z + l) : ℂ) = 1 := by
    intro z
    have := (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.map_finsum (hρfin z)
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
      Complex.ofRealHom_eq_coe] at this
    rw [← this, hρsum, Complex.ofReal_one]
  let g : L → (Fin n → ℂ) → ℂ := fun l z ↦ (ρ (z + l) : ℂ) * a l z
  have hgsupp : ∀ l z, g l z ≠ 0 → ‖z + l‖ < |R| + 2 := by
    intro l z h
    refine hβsupp l z fun h0 ↦ h ?_
    simp [g, ρ, h0]
  have hlfg := dca_locallyFinite L _ g hgsupp
  refine ⟨fun z ↦ -∑ᶠ l : L, g l z, ?_, fun m z ↦ ?_⟩
  · refine (dca_contDiff_finsum g (fun l ↦ ?_) hlfg).neg
    exact (Complex.ofRealCLM.contDiff.comp (hρc.comp (contDiff_id.add contDiff_const))).mul
      (ha l)
  · have hfin := dca_finite_support g hlfg z
    have e1 : ∀ l : L, g l (z + m) = g (l + m) z - (ρ (z + ↑(l + m)) : ℂ) * a m z := by
      intro l
      have : z + ↑m + ↑l = z + ↑(l + m) := by rw [Submodule.coe_add]; abel
      simp only [g, hcoc l m z, this]
      ring
    have hfin' : (Function.support fun l : L ↦ g (l + m) z).Finite :=
      (hfin.preimage (add_left_injective m).injOn).subset fun l hl ↦ hl
    have hfin'' : (Function.support fun l : L ↦ (ρ (z + ↑(l + m)) : ℂ) * a m z).Finite := by
      refine ((hρfin z).preimage (add_left_injective m).injOn).subset fun l hl h0 ↦ hl ?_
      simp only at h0 ⊢
      rw [h0, Complex.ofReal_zero, zero_mul]
    have r1 : ∑ᶠ l : L, g (l + m) z = ∑ᶠ l, g l z :=
      finsum_comp_equiv (Equiv.addRight m) (f := fun l ↦ g l z)
    have r2 : ∑ᶠ l : L, (ρ (z + ↑(l + m)) : ℂ) = 1 :=
      (finsum_comp_equiv (Equiv.addRight m) (f := fun l : L ↦ (ρ (z + l) : ℂ))).trans
        (hρsumC z)
    simp only [e1]
    rw [finsum_sub_distrib hfin' hfin'', r1, ← finsum_mul, r2]
    ring

end Lattice

end HodgeLean.Foundations

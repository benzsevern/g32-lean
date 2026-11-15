import HodgeLean.Foundations.AnalyticDivisorAlgebraicDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # Proof obligations for the analytic divisor spec

One obligation per statement of `HodgeLean.Foundations.AnalyticDivisorAlgebraic`. All eleven are proved, by three parallel provers.
-/

noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic

open AppellHumbert AutomorphyLineBundle

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem spec_isClosedAnalytic_zeroSet_aux (f : E → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    IsClosedAnalytic E {x | f x = 0} := by
  refine ⟨isClosed_eq (continuous_iff_continuousAt.2 fun x => (hf x (mem_univ x)).continuousAt)
      continuous_const, fun x _ => ⟨univ, isOpen_univ, mem_univ _, by simp, 1, fun _ => f,
      fun _ => hf, fun z _ => ?_⟩⟩
  simp

set_option linter.unusedVariables false in
theorem spec_interior_inter_zeroSet_eq_empty_aux {U : Set E} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hfx₀ : f x₀ ≠ 0) : interior (U ∩ {x | f x = 0}) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => hfx₀ ?_
  have hxU : x ∈ U := (interior_subset hx).1
  have hev : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hx] with y hy using hy.2
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hxU hev hx₀

theorem spec_interior_zeroSet_eq_empty_of_differentiable_aux {f : E → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) : interior {x | f x = 0} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x₀ hx₀ => hne (funext fun y => ?_)
  set g : ℂ → ℂ := fun t => f (x₀ + t • (y - x₀))
  have hγ : Continuous fun t : ℂ => x₀ + t • (y - x₀) := by fun_prop
  have hg : Differentiable ℂ g := fun t =>
    (hf _).comp t (((differentiableAt_id.smul_const (y - x₀)).const_add x₀))
  have hga : AnalyticOnNhd ℂ g univ := fun t _ => hg.analyticAt t
  have hev : g =ᶠ[𝓝 0] 0 := by
    have h0 : (fun t : ℂ => x₀ + t • (y - x₀)) 0 = x₀ := by simp
    have hmem : {x | f x = 0} ∈ 𝓝 ((fun t : ℂ => x₀ + t • (y - x₀)) 0) := by
      rw [h0]; exact mem_interior_iff_mem_nhds.1 hx₀
    filter_upwards [hγ.continuousAt.preimage_mem_nhds hmem] with t ht using ht
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ 0) hev (mem_univ 1)
  simpa [g] using this

end NormedSpace

section Theta

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

set_option linter.unusedSectionVars false in
theorem spec_theta_add_eq_zero_iff_aux (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D)
    (l : D.lattice) (v : V) : θ (v + l) = 0 ↔ θ v = 0 := by
  rw [hθ.2 l v]
  exact mul_eq_zero_iff_left (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))

theorem spec_preimage_thetaDivisor_aux (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) :
    proj D.lattice ⁻¹' thetaDivisor D θ = {v | θ v = 0} := by
  ext v
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hmem : -w + v ∈ D.lattice.toAddSubgroup := QuotientAddGroup.eq.mp hwv
    have hv : v = w + ((⟨-w + v, hmem⟩ : D.lattice) : V) := by simp
    change θ v = 0
    rw [hv, spec_theta_add_eq_zero_iff_aux D hθ]
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem spec_isClosed_thetaDivisor_aux (D : Datum (V := V)) {θ : V → ℂ} (hθ : θ ∈ sections D) :
    IsClosed (thetaDivisor D θ) := by
  rw [← (QuotientAddGroup.isQuotientMap_mk D.lattice.toAddSubgroup).isClosed_preimage]
  change IsClosed (proj D.lattice ⁻¹' thetaDivisor D θ)
  rw [spec_preimage_thetaDivisor_aux D hθ]
  exact isClosed_eq hθ.1.continuous continuous_const

theorem spec_interior_thetaDivisor_eq_empty_aux (D : Datum (V := V)) {θ : V → ℂ}
    (hθ : θ ∈ sections D) (hne : θ ≠ 0) : interior (thetaDivisor D θ) = ∅ := by
  have hcont : Continuous (proj D.lattice) := continuous_quotient_mk'
  have hsub : proj D.lattice ⁻¹' interior (thetaDivisor D θ) ⊆ interior {v | θ v = 0} := by
    apply interior_maximal
    · rw [← spec_preimage_thetaDivisor_aux D hθ]
      exact preimage_mono interior_subset
    · exact isOpen_interior.preimage hcont
  rw [spec_interior_zeroSet_eq_empty_of_differentiable_aux hθ.1 hne] at hsub
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact hsub hx

end Theta

theorem spec_isClosedAnalytic_theta_genusOne_aux (D : Datum (V := ℂ)) {θ : ℂ → ℂ}
    (hθ : θ ∈ sections D) : IsClosedAnalytic ℂ {z | θ z = 0} := by
  exact spec_isClosedAnalytic_zeroSet_aux θ (fun z _ ↦ hθ.1.analyticAt z)

/-- `ℤ ⊆ ℂ` is the zero set of `sin (π z)`. -/
theorem range_intCast_eq_setOf_sin_eq_zero :
    range ((↑) : ℤ → ℂ) = {z : ℂ | Complex.sin (Real.pi * z) = 0} := by
  ext z
  simp only [mem_range, mem_ofPred_eq, Complex.sin_eq_zero_iff]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, mul_comm _ _⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (mul_left_cancel₀ hπ (hk.trans (mul_comm _ _))).symm⟩

theorem spec_isClosedAnalytic_range_intCast_aux :
    IsClosedAnalytic ℂ (range ((↑) : ℤ → ℂ)) := by
  rw [range_intCast_eq_setOf_sin_eq_zero]
  refine spec_isClosedAnalytic_zeroSet_aux _ fun z _ => ?_
  exact (Complex.differentiable_sin.comp (differentiable_id.const_mul _)).analyticAt z

theorem spec_range_intCast_not_zariskiClosed_aux :
    ¬ ∃ S : Set (Polynomial ℂ), range ((↑) : ℤ → ℂ) = {z | ∀ p ∈ S, p.eval z = 0} := by
  rintro ⟨S, hS⟩
  have hzero : ∀ p ∈ S, p = 0 := fun p hp => by
    refine Polynomial.eq_zero_of_infinite_isRoot p ((infinite_range_of_injective
      Int.cast_injective).mono ?_)
    rintro _ ⟨k, rfl⟩
    have : (k : ℂ) ∈ {z | ∀ p ∈ S, p.eval z = 0} := hS ▸ mem_range_self k
    exact this p hp
  obtain ⟨k, hk⟩ : (1 / 2 : ℂ) ∈ range ((↑) : ℤ → ℂ) := hS ▸ fun p hp => by simp [hzero p hp]
  have hre := congrArg Complex.re hk
  simp at hre
  have h2 : (2 * k : ℝ) = 1 := by rw [hre]; norm_num
  have : (2 * k : ℤ) = 1 := by exact_mod_cast h2
  omega

open AlgebraicGeometry TopologicalSpace in
/-- Near a point of a closed set `C` of a locally noetherian scheme, inside an affine open `W`, the
set `C` is the common zero locus of finitely many sections over `W`. -/
theorem exists_finset_basicOpen {Y : Scheme} [IsLocallyNoetherian Y] {C : Set Y} (hC : IsClosed C)
    {W : Y.Opens} (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(Y, W), ∀ y ∈ W, (y ∈ C ↔ ∀ f ∈ s, y ∉ Y.basicOpen f) := by
  have := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : NoetherianSpace (W : Set Y) := noetherianSpace_of_isAffineOpen W hW
  set O : Y.Opens := W ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hcpt : IsCompact (O : Set Y) := by
    have h1 : IsCompact (((↑) : W → Y) '' (((↑) : W → Y) ⁻¹' (O : Set Y))) :=
      (NoetherianSpace.isCompact _).image continuous_subtype_val
    rwa [image_preimage_eq_of_subset (fun y hy => by simpa using hy.1)] at h1
  obtain ⟨s, hs⟩ := hcpt.elim_finite_subcover (fun f : {f : Γ(Y, W) // Y.basicOpen f ≤ O} =>
      (Y.basicOpen f.1 : Set Y)) (fun _ => (Y.basicOpen _).isOpen) (fun y hy => by
    obtain ⟨f, hfO, hyf⟩ := hW.exists_basicOpen_le (V := O) ⟨y, hy⟩ hy.1
    exact mem_iUnion.2 ⟨⟨f, hfO⟩, hyf⟩)
  refine ⟨s.map ⟨Subtype.val, Subtype.val_injective⟩, fun y hyW => ⟨?_, ?_⟩⟩
  · intro hyC f hf hyf
    obtain ⟨g, -, rfl⟩ := Finset.mem_map.1 hf
    exact (g.2 hyf).2 hyC
  · intro h
    by_contra hyC
    obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.1 (hs ⟨hyW, hyC⟩)
    exact h g.1 (Finset.mem_map_of_mem _ hg) hyg

open AlgebraicGeometry CategoryTheory TopologicalSpace in
theorem spec_isClosedAnalytic_preimage_underlying_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {C : Set X.left} (hC : IsClosed C) :
    IsClosedAnalytic (Fin (dim X.left) → ℂ)
      ((Point.underlying : ComplexPoint X → X.left) ⁻¹' C) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  rw [isClosedAnalytic_iff_finite]
  refine ⟨?_, fun z hz => ?_⟩
  · rw [← isOpen_compl_iff]
    exact Point.isOpen_overOpen (X := X) ⟨Cᶜ, hC.isOpen_compl⟩
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top z.underlying)
  obtain ⟨s, hs⟩ := exists_finset_basicOpen hC hW
  have hzs : z ∈ (chartAt (Fin (dim X.left) → ℂ) z).source := mem_chart_source _ z
  set e := chartAt (Fin (dim X.left) → ℂ) z
  refine ⟨e.target ∩ e.symm ⁻¹' Point.overOpen W,
    e.isOpen_inter_preimage_symm (Point.isOpen_overOpen W),
    ⟨e.map_source hzs, by rw [mem_preimage, e.left_inv hzs]; exact hzW⟩, inter_subset_left,
    s, inferInstance, fun i v => Point.evaluate W i.1 (e.symm v),
    fun i v hv => ComplexPoint.analyticAt_localChart_symm_evaluate X _ z hv.1 W i.1 hv.2,
    fun v hv => ?_⟩
  rw [mem_preimage, hs _ hv.2]
  refine ⟨fun h i => ?_, fun h f hf hvf => ?_⟩
  · by_contra hne
    exact h i.1 i.2 ((Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero i.1 _ hv.2).2 hne)
  · exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f _ hv.2).1 hvf (h ⟨f, hf⟩)

end HodgeLean.Foundations.AnalyticDivisorAlgebraic

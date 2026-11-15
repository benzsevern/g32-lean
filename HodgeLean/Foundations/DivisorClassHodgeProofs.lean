import HodgeLean.Foundations.DivisorClassHodgeDefs
import HodgeLean.Foundations.DivisorClassHodgeCocycle
import HodgeLean.Foundations.DivisorClassHodgeFactor
import HodgeLean.Foundations.DivisorClassHodgeLocal
import HodgeLean.Foundations.DivisorClassHodgePeriods
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8CurvatureProofs
import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian
import HodgeLean.Adapters.RiemannFormHermitian
import HodgeLean.Adapters.TorusCohomology
import HodgeLean.Foundations.AutomorphyChernClass
import HodgeLean.Foundations.ComplexSheafSingular
import HodgeLean.Foundations.SeveralVariableDbar
import HodgeLean.Foundations.DivisorClassHodgeTorusLattice

/-! # Divisor classes on abelian varieties are Hodge classes: open bodies (DC1)

One `_aux` theorem per statement of `DivisorClassHodge.lean`; the bodies are open. The route of
each is in `docs/specs/DivisorClassHodge.md`. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Filter Set Topology
open scoped ContDiff

namespace HodgeLean.Foundations

section Lattice

variable {n : ℕ} (L : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dc1_periodic_entire_const_aux (h : (Fin n → ℂ) → ℂ) (hh : Differentiable ℂ h)
    (hper : ∀ (l : L) z, h (z + l) = h z) (z w : Fin n → ℂ) : h z = h w :=
  dca_periodic_entire_const L h hh hper z w

theorem dc1_smooth_coboundary_aux (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, ContDiff ℝ ∞ (a l))
    (hcoc : ∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) :
    ∃ φ : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ φ ∧ ∀ (l : L) z, φ (z + l) - φ z = a l z :=
  dca_smooth_coboundary L a ha hcoc

theorem dc1_torus_dbar_aux (w : Fin n → (Fin n → ℂ) → ℂ) (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hper : ∀ j (l : L) z, w j (z + l) = w j z)
    (hclosed : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ (c : Fin n → ℂ) (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ ∞ ψ ∧
      (∀ (l : L) z, ψ (z + l) = ψ z) ∧ ∀ j z, w j z = c j + dbar_coord n j ψ z :=
  dct_lattice_dbar L w hw hper hclosed

theorem dc1_additiveCocycle_aux (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, Differentiable ℂ (a l))
    (hcoc : ∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) :
    ∃ (h : (Fin n → ℂ) → ℂ) (A : L →+ ℂ), Differentiable ℂ h ∧
      ∀ (l : L) z, a l z = h (z + l) - h z + A l :=
  dca_additiveCocycle L (dc1_torus_dbar_aux L) (dc1_smooth_coboundary_aux L) a ha hcoc

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem dc1_holomorphic_poincare_aux (u : Fin n → (Fin n → ℂ) → ℂ)
    (hu : ∀ j, Differentiable ℂ (u j))
    (hclosed : ∀ j k z, fderiv ℂ (u j) z (Pi.single k 1) = fderiv ℂ (u k) z (Pi.single j 1)) :
    ∃ h : (Fin n → ℂ) → ℂ, Differentiable ℂ h ∧
      ∀ j z, fderiv ℂ h z (Pi.single j 1) = u j z :=
  dca_holomorphic_poincare u hu hclosed

theorem dc1_linearization_aux (a F : L → (Fin n → ℂ) → ℂ)
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Differentiable ℂ (F l)) :
    ∃ (h : (Fin n → ℂ) → ℂ) (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ)) (b : L → ℂ),
      Differentiable ℂ h ∧ ∀ (l : L) z, F l z + h (z + l) - h z = lin l z + b l :=
  dca_linearization L (dc1_additiveCocycle_aux L) a F hcoc hlog hF

theorem dc1_typeOneOne_of_affine_aux (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : L, (B l m : ℂ) = lin m l - lin l m) :
    IsTypeOneOne (fun v w ↦ B v w) :=
  dca_typeOneOne_of_affine L lin B hB

theorem dc1_chernForm_typeOneOne_aux (a F : L → (Fin n → ℂ) → ℂ)
    (ha : ∀ l, Differentiable ℂ (a l))
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = chernForm F l m) :
    IsTypeOneOne (fun v w ↦ B v w) :=
  dca_chernForm_typeOneOne L a F (dc1_linearization_aux L a F hcoc hlog fun l ↦
    dca_log_differentiable (ha l) (hlog l) (hF l)) hcoc hlog hF B hB

end Lattice

section Factor

variable {n : ℕ} (L : Submodule ℤ (Fin n → ℂ))

omit L in
theorem dc1_squarefree_reduction_aux (p : Fin n → ℂ) (g : (Fin n → ℂ) → ℂ)
    (hg : AnalyticAt ℂ g p) (hne : ¬ ∀ᶠ z in 𝓝 p, g z = 0) :
    ∃ (g' : (Fin n → ℂ) → ℂ) (hg' : AnalyticAt ℂ g' p),
      Squarefree (⟨Filter.Germ.ofFun g', g', hg', rfl⟩ : AnalyticGermAt n p) ∧
        ∀ᶠ z in 𝓝 p, (g' z = 0 ↔ g z = 0) := by
  exact dcf_squarefree_reduction p g hg hne

theorem dc1_translate_associated_aux (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l : L) (p : Fin n → ℂ) :
    AreAssociatedAt f (fun z ↦ f (z + l)) p := by
  have hfl : AnalyticAt ℂ (fun z ↦ f (z + l)) p :=
    (hf _ (mem_univ _)).comp_of_eq (analyticAt_id.add analyticAt_const) rfl
  exact spec_bh5_reduced_associated n p f (fun z ↦ f (z + l)) (hf p (mem_univ p)) hfl (hred p)
    (dcf_squarefree_translate f hf l p hfl (hred (p + l)))
    (Eventually.of_forall fun z ↦ (hper l z).symm)

theorem dc1_factor_spec_aux (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l : L) :
    Differentiable ℂ (dc1_factor f L l) ∧ (∀ z, dc1_factor f L l z ≠ 0) ∧
      ∀ z, f (z + l) = dc1_factor f L l z * f z := by
  have hne : ∀ w, (𝓝[{w | f w ≠ 0}] w).NeBot :=
    fun w ↦ dcf_neBot_of_squarefree w f (hf w (mem_univ w)) (hred w)
  have hloc : ∀ z, ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      dc1_factor f L l =ᶠ[𝓝 z] u ∧ f (z + l) = u z * f z := by
    intro z
    obtain ⟨u, hu, hu0, heq⟩ := dc1_translate_associated_aux L f hf hred hper l z
    have heq' : (fun w ↦ f (w + l)) =ᶠ[𝓝 z] fun w ↦ (u w)⁻¹ * f w := by
      filter_upwards [heq, hu.continuousAt.eventually_ne hu0] with w hw hw0
      rw [hw, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
    refine ⟨fun w ↦ (u w)⁻¹, hu.inv hu0, inv_ne_zero hu0, ?_, heq'.eq_of_nhds⟩
    exact dcf_factor_eventuallyEq f L l hne _ z (hu.inv hu0) heq'
  refine ⟨fun z ↦ ?_, fun z ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨u, hu, -, he, -⟩ := hloc z
    exact hu.differentiableAt.congr_of_eventuallyEq he
  · obtain ⟨u, -, hu0, he, -⟩ := hloc z
    rw [he.eq_of_nhds]; exact hu0
  · obtain ⟨u, -, -, he, hfe⟩ := hloc z
    rw [he.eq_of_nhds]; exact hfe

theorem dc1_factor_cocycle_aux (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p))
    (hper : ∀ (l : L) p, f (p + l) = 0 ↔ f p = 0) (l m : L) (z : Fin n → ℂ) :
    dc1_factor f L (l + m) z = dc1_factor f L l (z + m) * dc1_factor f L m z := by
  haveI := dcf_neBot_of_squarefree z f (hf z (mem_univ z)) (hred z)
  obtain ⟨hd1, -, he1⟩ := dc1_factor_spec_aux L f hf hred hper (l + m)
  obtain ⟨hd2, -, he2⟩ := dc1_factor_spec_aux L f hf hred hper l
  obtain ⟨hd3, -, he3⟩ := dc1_factor_spec_aux L f hf hred hper m
  have hc2 : Continuous (fun w ↦ dc1_factor f L l (w + m) * dc1_factor f L m w) :=
    (hd2.continuous.comp (continuous_id.add continuous_const)).mul hd3.continuous
  have key : ∀ w, f w ≠ 0 →
      dc1_factor f L (l + m) w = dc1_factor f L l (w + m) * dc1_factor f L m w := by
    intro w hw
    apply mul_right_cancel₀ hw
    rw [← he1 w, mul_assoc, ← he3 w, ← he2 (w + m)]
    congr 1
    push_cast
    abel
  exact tendsto_nhds_unique_of_eventuallyEq
    (hd1.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hc2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := {w | f w ≠ 0}) key)

theorem dc1_factorLog_spec_aux (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, Differentiable ℂ (a l))
    (ha₀ : ∀ l z, a l z ≠ 0) (l : L) :
    Differentiable ℂ (dc1_factorLog a l) ∧
      ∀ z, a l z = Complex.exp (2 * Real.pi * Complex.I * dc1_factorLog a l z) := by
  obtain ⟨h, hh, hexp⟩ := dcf_exists_log (a l) (ha l) (ha₀ l)
  have hform : ∀ z, dc1_factorLog a l z =
      (Complex.log (a l 0) + (h z - h 0)) * (2 * Real.pi * Complex.I)⁻¹ := by
    intro z
    rw [dc1_factorLog, dcf_integral_logDeriv (a l) h hh hexp z, div_eq_mul_inv]
  refine ⟨?_, fun z ↦ ?_⟩
  · rw [funext hform]
    exact ((differentiable_const _).add (hh.sub_const _)).mul_const _
  · rw [hform, ← mul_assoc, mul_comm _ (Complex.log (a l 0) + (h z - h 0)), mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, mul_one, Complex.exp_add, Complex.exp_sub,
      Complex.exp_log (ha₀ l 0), hexp, hexp]
    field_simp [ha₀ l 0]

theorem dc1_chernBihom_apply_aux [Module.Free ℤ L] [Module.Finite ℤ L]
    (a F : L → (Fin n → ℂ) → ℂ)
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (l m : L) :
    dc1_chernBihom F l m = -chernForm F l m := by
  classical
  obtain ⟨E, hE⟩ := spec_chernForm_biadditive a F hcoc hlog hF
  let b := Module.Free.chooseBasis ℤ L
  have h1 : ∀ i, dc1_chernBihom F (b i) = -(E (b i)) := by
    intro i
    apply AddMonoidHom.toIntLinearMap_injective
    refine b.ext fun j ↦ ?_
    simp [b, dc1_chernBihom, Finsupp.single_apply, hE]
  have h2 : dc1_chernBihom F = -E := by
    apply AddMonoidHom.toIntLinearMap_injective
    refine b.ext fun i ↦ ?_
    simpa using h1 i
  rw [h2]
  simp [hE]

end Factor

section Abelian

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

theorem dc1_componentSupport_interior_aux (x : X.left) (hx : Order.coheight x = 1) :
    interior (bh4_componentSupport X x) = ∅ :=
  dcl_componentSupport_interior X x hx

theorem dc1_locallyPrincipal_aux (x : X.left) (hx : Order.coheight x = 1)
    (z : ComplexPoint X) :
    ∃ (V : X.left.Opens) (s : Γ(X.left, V)), z ∈ Point.overOpen V ∧
      ∀ w ∈ Point.overOpen V, (w ∈ bh4_componentSupport X x ↔ Point.evaluate V s w = 0) :=
  dcl_locallyPrincipal X x hx z

theorem dc1_local_equation_aux (x : X.left) (hx : Order.coheight x = 1)
    (p : Fin (dim X.left) → ℂ) :
    ∃ g : (Fin (dim X.left) → ℂ) → ℂ, AnalyticAt ℂ g p ∧ (¬ ∀ᶠ z in 𝓝 p, g z = 0) ∧
      ∀ᶠ z in 𝓝 p, (g z = 0 ↔ z ∈ dc1_coverDivisor X x) := by
  obtain ⟨V, s, hpV, hiff⟩ := dc1_locallyPrincipal_aux X x hx (abelianExp X p)
  have hV : ∀ᶠ q in 𝓝 p, abelianExp X q ∈ Point.overOpen V :=
    (continuous_abelianExp X).continuousAt.preimage_mem_nhds
      ((Point.isOpen_overOpen V).mem_nhds hpV)
  refine ⟨fun q ↦ Point.evaluate V s (abelianExp X q),
    bh8_analyticAt_evaluate_abelianExp X V s p hpV, ?_, ?_⟩
  · intro hzero
    obtain ⟨U, hU, hUo, hpU⟩ := mem_nhds_iff.mp (hzero.and hV)
    have hsub : abelianExp X '' U ⊆ bh4_componentSupport X x := by
      rintro _ ⟨q, hq, rfl⟩
      exact (hiff _ (hU hq).2).2 (hU hq).1
    have hint := interior_maximal hsub (isOpenMap_abelianExp X U hUo)
    rw [dc1_componentSupport_interior_aux X x hx] at hint
    exact hint ⟨p, hpU, rfl⟩
  · filter_upwards [hV] with q hq
    exact (hiff _ hq).symm

theorem dc1_cover_equation_aux (x : X.left) (hx : Order.coheight x = 1) :
    ∃ (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ),
      (∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧ ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x := by
  apply spec_bh5_reduced_principalization
  intro p
  obtain ⟨g, hg, hne, hev⟩ := dc1_local_equation_aux X x hx p
  obtain ⟨g', hg', hsq, hev'⟩ := dc1_squarefree_reduction_aux p g hg hne
  refine ⟨g', hg', hsq, ?_⟩
  filter_upwards [hev, hev'] with z h h'
  exact h'.trans h

theorem dc1_periodPair_latticeClassHQ_aux
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l : abelianPeriodLattice X, E l l = 0) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (latticeClassHQ X E) = (E l m : ℚ) :=
  dcp_periodPair_latticeClassHQ X E hE l m

theorem dc1_boundary_chern_aux (a F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hcoc : ∀ (l m : abelianPeriodLattice X) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : ∀ (l : abelianPeriodLattice X) z, θ (z + l) = a l z * θ z)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryIncrement g = -(chernForm F l m : ℂ) :=
  dcp_boundary_chern X a F hcoc hlog hF θ hθ l m z g hg hexp

theorem dc1_period_cycleClass_aux (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x)
    (F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, dc1_factor f (abelianPeriodLattice X) l v =
      Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (cycleComponentSheafClass X x hx) = -(chernForm F l m : ℚ) := by
  have hper := dcp_zero_periodic X x f hzero
  have hdiff : Differentiable ℂ f := fun p ↦ (hf p (mem_univ p)).differentiableAt
  have hne := dcp_ne_zero_of_squarefree f 0 (hf 0 (mem_univ 0)) (hred 0)
  obtain ⟨z, hz⟩ := spec_bh4_boundary_avoiding X f hdiff hne l m
  obtain ⟨g, hg, hexp⟩ := spec_bh4_boundary_logs X f hdiff.continuous l m z hz
  have hev := spec_bh4_supported_square_evaluation X x hx f hf hred hzero l m z hz
  rw [spec_bh4_winding_orientation X f hdiff l m z g hg hexp] at hev
  have hcoc := dc1_factor_cocycle_aux (abelianPeriodLattice X) f hf hred hper
  have hθ : ∀ (l : abelianPeriodLattice X) z,
      f (z + l) = dc1_factor f (abelianPeriodLattice X) l z * f z :=
    fun l ↦ (dc1_factor_spec_aux (abelianPeriodLattice X) f hf hred hper l).2.2
  rw [dc1_boundary_chern_aux X _ F hcoc hlog hF f hθ l m z g hg hexp] at hev
  exact_mod_cast hev

theorem dc1_cycleClass_eq_chernClass_aux (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    cycleComponentSheafClass X x hx = dc1_chernClass X f := by
  have hper := dcp_zero_periodic X x f hzero
  set a := dc1_factor f (abelianPeriodLattice X) with ha
  have hspec := dc1_factor_spec_aux (abelianPeriodLattice X) f hf hred hper
  have hcoc := dc1_factor_cocycle_aux (abelianPeriodLattice X) f hf hred hper
  have hlogspec := dc1_factorLog_spec_aux (abelianPeriodLattice X) a
    (fun l ↦ (hspec l).1) (fun l ↦ (hspec l).2.1)
  have hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * dc1_factorLog a l v) :=
    fun l ↦ (hlogspec l).2
  have hF : ∀ l, Continuous (dc1_factorLog a l) := fun l ↦ (hlogspec l).1.continuous
  have hbi := dc1_chernBihom_apply_aux (abelianPeriodLattice X) a (dc1_factorLog a) hcoc hlog hF
  have halt : ∀ l : abelianPeriodLattice X, dc1_chernBihom (dc1_factorLog a) l l = 0 := by
    intro l
    rw [hbi]
    simp [chernForm, logForm]
  apply spec_bh4_periodPair_ext X
  intro l m
  rw [dc1_period_cycleClass_aux X x hx f hf hred hzero (dc1_factorLog a) hlog hF l m]
  change _ = bh4_periodPair X l m (latticeClassHQ X (dc1_chernBihom (dc1_factorLog a)))
  rw [dc1_periodPair_latticeClassHQ_aux X _ halt l m, hbi]
  push_cast
  rfl

/-- The Chern form of the factor of a reduced cover equation is alternating and its real
extension satisfies the Riemann relation.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.1.2 and §2.2;
`dc1_chernForm_typeOneOne`, `spec_exists_unique_realExtension`. -/
theorem dcp_chernBihom_riemann (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hper : ∀ (l : abelianPeriodLattice X) p, f (p + l) = 0 ↔ f p = 0) :
    (∀ l, dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X))) l l = 0) ∧
      ∃ B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ,
        (∀ l m : abelianPeriodLattice X, B l m =
          dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X))) l m) ∧
        IsTypeOneOne (fun v w ↦ B v w) := by
  set a := dc1_factor f (abelianPeriodLattice X) with ha
  have hspec := dc1_factor_spec_aux (abelianPeriodLattice X) f hf hred hper
  have hcoc := dc1_factor_cocycle_aux (abelianPeriodLattice X) f hf hred hper
  have hlogspec := dc1_factorLog_spec_aux (abelianPeriodLattice X) a
    (fun l ↦ (hspec l).1) (fun l ↦ (hspec l).2.1)
  have hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * dc1_factorLog a l v) :=
    fun l ↦ (hlogspec l).2
  have hF : ∀ l, Continuous (dc1_factorLog a l) := fun l ↦ (hlogspec l).1.continuous
  have hbi := dc1_chernBihom_apply_aux (abelianPeriodLattice X) a (dc1_factorLog a) hcoc hlog hF
  have halt : ∀ l : abelianPeriodLattice X, dc1_chernBihom (dc1_factorLog a) l l = 0 := by
    intro l
    rw [hbi]
    simp [chernForm, logForm]
  refine ⟨halt, ?_⟩
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI : DiscreteTopology (abelianPeriodLattice X) :=
    discrete_complexExponentialLattice X (dim X.left)
  letI : IsZLattice ℝ (abelianPeriodLattice X) :=
    isZLattice_complexExponentialLattice X (dim X.left)
  obtain ⟨B, hB, -⟩ := spec_exists_unique_realExtension (abelianPeriodLattice X)
    (dc1_chernBihom (dc1_factorLog a))
  refine ⟨B, hB, ?_⟩
  have hB' : ∀ l m : abelianPeriodLattice X, (-B) l m = chernForm (dc1_factorLog a) l m := by
    intro l m
    rw [LinearMap.neg_apply, LinearMap.neg_apply, hB, hbi]
    push_cast
    ring
  have h11 := dc1_chernForm_typeOneOne_aux (abelianPeriodLattice X) a (dc1_factorLog a)
    (fun l ↦ (hspec l).1) hcoc hlog hF (-B) hB'
  intro v w
  have := h11 v w
  simp only [LinearMap.neg_apply] at this
  linarith

theorem dc1_appellHumbert_datum_aux (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    ∃ A : bh4_AHData X,
      A.E = dc1_chernBihom (dc1_factorLog (dc1_factor f (abelianPeriodLattice X))) ∧
        cycleComponentSheafClass X x hx = latticeClassHQ X A.E := by
  obtain ⟨halt, B, hB, h11⟩ := dcp_chernBihom_riemann X f hf hred (dcp_zero_periodic X x f hzero)
  obtain ⟨H, hE, -, χ, hχ, -⟩ := spec_exists_datumOfX_of_riemann X _ halt B hB h11
  exact ⟨⟨H, _, hE, χ, hχ⟩, rfl, dc1_cycleClass_eq_chernClass_aux X x hx f hf hred hzero⟩

theorem dc1_chernClass_mem_hdg_aux (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) :
    (dc1_chernClass X f : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := by
  obtain ⟨halt, B, hB, h11⟩ := dcp_chernBihom_riemann X f hf hred (dcp_zero_periodic X x f hzero)
  exact spec_latticeClassHQ_mem_hdg_of_riemann X (finiteBetti_abelian X)
    (spec_bettiDeRhamIso_abelian X) _ B hB halt h11

theorem dc1_cycleComponentSheafClass_mem_hdg_aux (x : X.left) (hx : Order.coheight x = 1) :
    cycleComponentSheafClass X x hx ∈ Hdg^1(X; ℚ) := by
  obtain ⟨f, hf, hred, hzero⟩ := dc1_cover_equation_aux X x hx
  rw [dc1_cycleClass_eq_chernClass_aux X x hx f hf hred hzero]
  exact dc1_chernClass_mem_hdg_aux X x hx f hf hred hzero

end Abelian

theorem dc1_divisorClass_le_hodge_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ) := by
  apply sSup_le
  rintro _ ⟨y, hy, rfl⟩
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact dc1_cycleComponentSheafClass_mem_hdg_aux X y hy

end HodgeLean.Foundations

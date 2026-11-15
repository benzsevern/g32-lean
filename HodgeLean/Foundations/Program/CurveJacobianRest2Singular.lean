import HodgeLean.Foundations.Program.CurveJacobianRest2IntegCurve
import HodgeLean.Foundations.Program.CurveJacobianRest2Key
import HodgeLean.Foundations.Program.CurveJacobianRest2Weight

/-! # Track B3, lane Rest2: holomorphic periods and singular periods of loops

On a compact connected Riemann surface `C`:
* every rational singular `1`-cocycle `ψ` has a holomorphic form `θ` with
  `ψ(p) = Re ∫_γ θ` on every loop `p` with a `C¹` representative `γ` (`b3Rest2_cocycle_form`):
  the closed form of `ψ` (`CurveJacobianRest2Cech.lean`) is `Re θ + dg` (Hodge decomposition);
* so loops with the same holomorphic periods have the same singular periods `loopPeriod`
  (`loopPeriod p [ψ] = s ψ(p)` for a universal `s ≠ 0`);
* conversely, equal singular periods make the two loops homologous over `ℚ`, hence over `ℂ`, and
  the integration cocycle of each holomorphic form (`CurveJacobianRest2IntegCurve.lean`) takes the
  same value on them: the holomorphic periods agree (`b3Rest2_period_eq_iff_loopPeriod`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold Metric CategoryTheory
open scoped Topology ContDiff Simplicial TensorProduct

namespace HodgeLean.Foundations.Program

open HodgeLean.Adapters

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The continuous loop of a `C¹` loop. -/
def b3Rest2_circ (γ : b3_SmoothLoop E C) : C(UnitAddCircle, C) :=
  ⟨γ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact γ.2.2.continuous⟩

theorem b3Rest2_circ_apply (γ : b3_SmoothLoop E C) (t : ℝ) : γ.1 t = b3Rest2_circ γ t := rfl

variable [FiniteDimensional ℂ E] [T2Space C] [CompactSpace C] [ConnectedSpace C]
variable (hE : Module.finrank ℂ E = 1)
include hE

attribute [local instance] b3Forms_isManifold_real

/-- **Every rational `1`-cocycle has the real periods of a holomorphic form on loops.** -/
theorem b3Rest2_cocycle_form
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of C)) 1) :
    ∃ θ : b3_HolForm E C, ∀ (γ : b3_SmoothLoop E C) (p : C(UnitAddCircle, C)),
      (∀ t, γ.1 t = p t) →
        ((ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) : ℚ) : ℝ) =
          (b3_period E C γ θ).re := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  haveI : Fact (Module.finrank ℂ E = 1) := ⟨hE⟩
  obtain ⟨K⟩ := b3Rest2_exists_cov (E := E) (C := C)
  obtain ⟨U⟩ := b3Rest2_exists_pou K
  obtain ⟨θ, g, hg, heq⟩ := b3Rest_hodge (U.isSmooth_α ψ) (U.d_α ψ)
  refine ⟨θ, fun γ p hp ↦ ?_⟩
  rw [U.loop_formula ψ γ.2.2 γ.2.1 p hp, heq,
    b3Forms_lineIntegral_add (b3Forms_isSmooth_reForm θ) hg.d γ.2.2,
    b3Forms_lineIntegral_d hg γ.2.2, b3Rest2_re_period]
  have : γ.1 1 = γ.1 0 := by simpa using γ.2.1 0
  rw [this, sub_self, add_zero]

/-- **Loops with equal holomorphic periods have equal singular periods.** -/
theorem b3Rest2_loopPeriod_eq_of_period_eq (γ δ : b3_SmoothLoop E C) (p q : C(UnitAddCircle, C))
    (hp : ∀ t, γ.1 t = p t) (hq : ∀ t, δ.1 t = q t) (h : b3_period E C γ = b3_period E C δ) :
    loopPeriod p = loopPeriod q := by
  obtain ⟨s, hs0, hs⟩ := spec_loopPeriod_cohomologyClass_aux
  ext c
  obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective (TopCat.of C) 1 c
  rw [hs C p ψ, hs C q ψ]
  obtain ⟨θ, hθ⟩ := b3Rest2_cocycle_form hE ψ
  have e := (hθ γ p hp).trans ((congrArg (fun f ↦ (f θ).re) h).trans (hθ δ q hq).symm)
  congr 1
  exact_mod_cast e

/-- The instances of the period lattice of a compact connected Riemann surface. -/
theorem b3Rest2_lattice_instances :
    Module.Finite ℤ (b3_periodLattice E C) ∧ Module.Free ℤ (b3_periodLattice E C) ∧
      DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
  exact ⟨inferInstance, inferInstance,
    b2_latticeMap_discrete _ (b3Rest2_isWeightOne hE (b3Rest2_key hE))⟩

/-- **Loops with equal singular periods have equal holomorphic periods.** -/
theorem b3Rest2_period_eq_of_loopPeriod_eq (γ δ : b3_SmoothLoop E C) (p q : C(UnitAddCircle, C))
    (hp : ∀ t, γ.1 t = p t) (hq : ∀ t, δ.1 t = q t) (h : loopPeriod p = loopPeriod q) :
    b3_period E C γ = b3_period E C δ := by
  obtain ⟨s, hs0, hs⟩ := spec_loopPeriod_cohomologyClass_aux
  have key : ∀ f : Module.Dual ℚ (AlgebraicTopology.Singular.Homology ℚ (TopCat.of C) 1),
      f (((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (loopCycle ℚ p)) =
      f (((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (loopCycle ℚ q)) := by
    intro f
    obtain ⟨c, rfl⟩ :=
      (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ (TopCat.of C) 1).surjective f
    obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective (TopCat.of C) 1 c
    rw [cohomologyEquivDualHomology_cohomologyClass, cohomologyEquivDualHomology_cohomologyClass]
    have e := LinearMap.congr_fun h (Singular.cohomologyClass (TopCat.of C) 1 ψ)
    rw [hs C p ψ, hs C q ψ] at e
    exact mul_left_cancel₀ hs0 e
  have hzq : ((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1).moduleCatHomologyClass
      (loopCycle ℚ p) =
      ((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (loopCycle ℚ q) := by
    set zp : AlgebraicTopology.Singular.Homology ℚ (TopCat.of C) 1 :=
      ((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (loopCycle ℚ p)
    set zq : AlgebraicTopology.Singular.Homology ℚ (TopCat.of C) 1 :=
      ((AlgebraicTopology.Singular.SingularChainComplex ℚ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (loopCycle ℚ q)
    have h0 : zp - zq = 0 := (Module.forall_dual_apply_eq_zero_iff ℚ (zp - zq)).1 fun f ↦ by
      rw [map_sub, key f, sub_self]
    exact sub_eq_zero.1 h0
  have hzc : ((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of C)).sc 1).moduleCatHomologyClass
      (loopCycle ℂ p) =
      ((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of C)).sc 1).moduleCatHomologyClass
        (loopCycle ℂ q) := by
    apply (complexHomologyEquivBaseChange (TopCat.of C) 1).symm.injective
    rw [complexHomologyEquivBaseChange_symm_loopCycle, complexHomologyEquivBaseChange_symm_loopCycle,
      hzq]
  obtain ⟨h1, h2, h3⟩ := b3Rest2_lattice_instances (C := C) hE
  obtain ⟨aj, haj⟩ := b3A_exists_abelJacobi hE (γ.1 0)
  have hajc : Continuous aj := (b3Rest_abelJacobi_holomorphic hE _ aj haj).continuous
  funext θ
  have e := congrArg (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) 1
    (Singular.cohomologyClass (TopCat.of C) 1
      (b3Rest2_integCocycle aj hajc (AddMonoidHom.id ℂ) θ))) hzc
  rw [cohomologyEquivDualHomology_cohomologyClass, cohomologyEquivDualHomology_cohomologyClass]
    at e
  have ep := b3Rest2_integCocycle_loop aj hajc hE (γ.1 0) haj (AddMonoidHom.id ℂ) θ γ p hp
  have eq := b3Rest2_integCocycle_loop aj hajc hE (γ.1 0) haj (AddMonoidHom.id ℂ) θ δ q hq
  exact ep.symm.trans (e.trans eq)

/-- **Holomorphic periods and singular periods of loops determine each other.** -/
theorem b3Rest2_period_eq_iff_loopPeriod (γ δ : b3_SmoothLoop E C) (p q : C(UnitAddCircle, C))
    (hp : ∀ t, γ.1 t = p t) (hq : ∀ t, δ.1 t = q t) :
    b3_period E C γ = b3_period E C δ ↔ loopPeriod p = loopPeriod q :=
  ⟨b3Rest2_loopPeriod_eq_of_period_eq hE γ δ p q hp hq,
    b3Rest2_period_eq_of_loopPeriod_eq hE γ δ p q hp hq⟩

/-! ## The dimension of `H¹(C; ℚ)` -/

omit hE in
theorem b3Rest2_period_add (γ : b3_SmoothLoop E C) (θ θ' : b3_HolForm E C) :
    b3_period E C γ (θ + θ') = b3_period E C γ θ + b3_period E C γ θ' := by
  have h := b3Forms_period_mem_linearDual γ 1 θ θ'
  simpa using h

omit hE in
theorem b3Rest2_period_smul (γ : b3_SmoothLoop E C) (a : ℂ) (θ : b3_HolForm E C) :
    b3_period E C γ (a • θ) = a * b3_period E C γ θ := by
  have h := b3Forms_period_mem_linearDual γ a θ 0
  rwa [add_zero, b3Forms_linearDual_apply_zero (b3Forms_period_mem_linearDual γ), add_zero] at h

omit hE in
theorem b3Rest2_period_rsmul (γ : b3_SmoothLoop E C) (r : ℝ) (θ : b3_HolForm E C) :
    b3_period E C γ (r • θ) = r * b3_period E C γ θ := by
  rw [← Complex.coe_smul, b3Rest2_period_smul]

/-- **A holomorphic form is determined by the real parts of its periods.** -/
theorem b3Rest2_eq_of_re_period {θ θ' : b3_HolForm E C}
    (h : ∀ γ : b3_SmoothLoop E C, (b3_period E C γ θ).re = (b3_period E C γ θ').re) : θ = θ' := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hper : b3Forms_PeriodsVanish (b3Forms_reForm (θ - θ')) := fun γ hp hγ ↦ by
    have e := h ⟨γ, hp, hγ⟩
    have hsub : θ - θ' = (-1 : ℂ) • θ' + θ := by
      rw [neg_one_smul, neg_add_eq_sub]
    have hl := b3Forms_period_mem_linearDual ⟨γ, hp, hγ⟩ (-1) θ' θ
    rw [← b3Rest2_re_period (θ - θ') ⟨γ, hp, hγ⟩, hsub, hl]
    simp only [neg_mul, one_mul, Complex.add_re, Complex.neg_re]
    linarith
  obtain ⟨g, hg, hdg⟩ := b3Forms_exists_primitive (b3Forms_isSmooth_reForm (θ - θ'))
    (b3Forms_d_reForm hE (θ - θ')) hper
  exact sub_eq_zero.1 (b3Forms_hol_eq_zero_of_reForm_exact hE (θ - θ') hg hdg)

omit hE in
/-- **Induction on the period lattice.** -/
theorem b3Rest2_lattice_induction (P : b3_periodLattice E C → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x))
    (hg : ∀ γ, P (b3_latticePeriod E C γ)) (x : b3_periodLattice E C) : P x := by
  obtain ⟨x, hx⟩ := x
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, rfl⟩ := hy
    exact hg γ
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd ⟨y, _⟩ ⟨z, _⟩ hy hz
  | neg y _ hy => exact hneg ⟨y, _⟩ hy

omit hE in
/-- The universal constant relating singular periods and cocycle values on loops. -/
def b3Rest2_s : ℚ := spec_loopPeriod_cohomologyClass_aux.choose

omit hE in
theorem b3Rest2_s_ne_zero : b3Rest2_s ≠ 0 := spec_loopPeriod_cohomologyClass_aux.choose_spec.1

omit hE in
theorem b3Rest2_s_spec (p : C(UnitAddCircle, C))
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of C)) 1) :
    loopPeriod p (Singular.cohomologyClass (TopCat.of C) 1 ψ) =
      b3Rest2_s * ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) :=
  spec_loopPeriod_cohomologyClass_aux.choose_spec.2 C p ψ

omit hE in
/-- **The holomorphic form of a rational class**: its real periods are the singular periods. -/
def b3Rest2_Pc (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1)
    (θ : b3_HolForm E C) : Prop :=
  ∀ γ : b3_SmoothLoop E C, ((loopPeriod (b3Rest2_circ γ) c : ℚ) : ℝ) =
    (b3Rest2_s : ℝ) * (b3_period E C γ θ).re

theorem b3Rest2_Pc_exists (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) :
    ∃ θ : b3_HolForm E C, b3Rest2_Pc c θ := by
  obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective (TopCat.of C) 1 c
  obtain ⟨θ, hθ⟩ := b3Rest2_cocycle_form hE ψ
  refine ⟨θ, fun γ ↦ ?_⟩
  rw [b3Rest2_s_spec, Rat.cast_mul, hθ γ _ (b3Rest2_circ_apply γ)]

theorem b3Rest2_Pc_unique {c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1}
    {θ θ' : b3_HolForm E C} (h : b3Rest2_Pc c θ) (h' : b3Rest2_Pc c θ') : θ = θ' := by
  refine b3Rest2_eq_of_re_period hE fun γ ↦ ?_
  have e := (h γ).symm.trans (h' γ)
  have hs : (b3Rest2_s : ℝ) ≠ 0 := by exact_mod_cast b3Rest2_s_ne_zero
  exact mul_left_cancel₀ hs e

/-- The holomorphic form of a rational class. -/
def b3Rest2_T (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) : b3_HolForm E C :=
  (b3Rest2_Pc_exists hE c).choose

theorem b3Rest2_T_spec (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) :
    b3Rest2_Pc c (b3Rest2_T hE c) :=
  (b3Rest2_Pc_exists hE c).choose_spec

theorem b3Rest2_T_add (c c' : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) :
    b3Rest2_T hE (c + c') = b3Rest2_T hE c + b3Rest2_T hE c' := by
  refine b3Rest2_Pc_unique hE (b3Rest2_T_spec hE _) fun γ ↦ ?_
  rw [map_add, Rat.cast_add, b3Rest2_T_spec hE c γ, b3Rest2_T_spec hE c' γ, b3Rest2_period_add,
    Complex.add_re]
  ring

theorem b3Rest2_T_smul (q : ℚ) (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) :
    b3Rest2_T hE (q • c) = ((q : ℂ)) • b3Rest2_T hE c := by
  refine b3Rest2_Pc_unique hE (b3Rest2_T_spec hE _) fun γ ↦ ?_
  rw [map_smul, smul_eq_mul, Rat.cast_mul, b3Rest2_T_spec hE c γ, b3Rest2_period_smul]
  simp only [Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
  ring

/-- **The values of the form of a class on the lattice are rational** (up to `s`). -/
theorem b3Rest2_rat (c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1)
    (l : b3_periodLattice E C) :
    ∃ q : ℚ, (q : ℝ) = (b3Rest2_s : ℝ) * (l.1 (b3Rest2_T hE c)).re := by
  refine b3Rest2_lattice_induction (fun l ↦ ∃ q : ℚ, (q : ℝ) =
    (b3Rest2_s : ℝ) * (l.1 (b3Rest2_T hE c)).re) ⟨0, by simp⟩ ?_ ?_ ?_ l
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, Complex.add_re, Rat.cast_add, ha, hb]
    ring
  · rintro x ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, Complex.neg_re, Rat.cast_neg, ha]
    ring
  · intro γ
    exact ⟨loopPeriod (b3Rest2_circ γ) c, b3Rest2_T_spec hE c γ⟩

omit hE in
theorem b3Rest2_lattice_add_apply (l : b3_periodLattice E C) (θ θ' : b3_HolForm E C) :
    l.1 (θ + θ') = l.1 θ + l.1 θ' := by
  have h := b3Forms_periodLattice_le_linearDual l.2 1 θ θ'
  simpa using h

omit hE in
theorem b3Rest2_lattice_smul_apply (l : b3_periodLattice E C) (a : ℂ) (θ : b3_HolForm E C) :
    l.1 (a • θ) = a * l.1 θ := by
  have hl := b3Forms_periodLattice_le_linearDual l.2
  have h := hl a θ 0
  rwa [add_zero, b3Forms_linearDual_apply_zero hl, add_zero] at h

/-- **A rational class whose form vanishes is zero.** -/
theorem b3Rest2_eq_zero_of_T {c : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1}
    (hc : b3Rest2_T hE c = 0) : c = 0 := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective (TopCat.of C) 1 c
  obtain ⟨K⟩ := b3Rest2_exists_cov (E := E) (C := C)
  obtain ⟨U⟩ := b3Rest2_exists_pou K
  have hs : (b3Rest2_s : ℝ) ≠ 0 := by exact_mod_cast b3Rest2_s_ne_zero
  have hper : b3Forms_PeriodsVanish (U.α ψ) := fun γ hp hγ ↦ by
    have h1 := b3Rest2_T_spec hE (Singular.cohomologyClass (TopCat.of C) 1 ψ) ⟨γ, hp, hγ⟩
    rw [hc, b3Rest2_s_spec, Rat.cast_mul] at h1
    have h2 : b3_period E C ⟨γ, hp, hγ⟩ 0 = 0 := by
      simp [b3_period, b3_pathPeriod, b3_pathIntegral]
    rw [h2, Complex.zero_re, mul_zero] at h1
    rw [← U.loop_formula ψ hγ hp (b3Rest2_circ ⟨γ, hp, hγ⟩) (b3Rest2_circ_apply ⟨γ, hp, hγ⟩)]
    exact (mul_eq_zero.1 h1).resolve_left hs
  obtain ⟨F, hF, hdF⟩ := b3Forms_exists_primitive (U.isSmooth_α ψ) (U.d_α ψ) hper
  exact U.cohomologyClass_eq_zero_of_exact ψ hF hdF.symm

/-- **`dim H¹(C; ℚ) ≤ 2g`.** -/
theorem b3Rest2_finrank_cohomology_le :
    Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) ∧
      Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) ≤
        2 * Module.finrank ℂ (b3_HolForm E C) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨h1, h2, -⟩ := b3Rest2_lattice_instances (C := C) hE
  set b := Module.Free.chooseBasis ℤ (b3_periodLattice E C)
  let Φ : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1 →ₗ[ℚ]
      (Module.Free.ChooseBasisIndex ℤ (b3_periodLattice E C) → ℚ) :=
    { toFun := fun c i ↦ (b3Rest2_rat hE c (b i)).choose
      map_add' := fun c c' ↦ by
        funext i
        apply Rat.cast_injective (α := ℝ)
        simp only [Pi.add_apply, Rat.cast_add]
        rw [(b3Rest2_rat hE (c + c') (b i)).choose_spec, (b3Rest2_rat hE c (b i)).choose_spec,
          (b3Rest2_rat hE c' (b i)).choose_spec, b3Rest2_T_add, b3Rest2_lattice_add_apply,
          Complex.add_re]
        ring
      map_smul' := fun q c ↦ by
        funext i
        apply Rat.cast_injective (α := ℝ)
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Rat.cast_mul]
        rw [(b3Rest2_rat hE (q • c) (b i)).choose_spec, (b3Rest2_rat hE c (b i)).choose_spec,
          b3Rest2_T_smul, b3Rest2_lattice_smul_apply]
        simp only [Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
        ring }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hs : (b3Rest2_s : ℝ) ≠ 0 := by exact_mod_cast b3Rest2_s_ne_zero
    have hb : ∀ i, b3Rest2_ρ (b i) (b3Rest2_T hE c) = 0 := fun i ↦ by
      have e1 := congrFun hc i
      have e2 := (b3Rest2_rat hE c (b i)).choose_spec
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at e1
      rw [e1, Rat.cast_zero, eq_comm, mul_eq_zero] at e2
      exact e2.resolve_left hs
    have hT : b3Rest2_T hE c = 0 := b3Rest2_eq_zero_of_re_lattice hE fun l ↦ by
      rw [← b3Rest2_ρ_apply, ← b.sum_repr l, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [map_zsmul, LinearMap.smul_apply, hb i, smul_zero]
    exact b3Rest2_eq_zero_of_T hE hT
  haveI : Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) :=
    Module.Finite.of_injective Φ hinj
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1)
      ≤ Module.finrank ℚ (Module.Free.ChooseBasisIndex ℤ (b3_periodLattice E C) → ℚ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℤ (b3_periodLattice E C) := by
        rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]
    _ = 2 * Module.finrank ℂ (b3_HolForm E C) := b3Rest2_finrank_eq hE (b3Rest2_key hE)

omit hE in
theorem b3Rest2_period_sum {ι : Type} (S : Finset ι) (γ : b3_SmoothLoop E C)
    (θ : ι → b3_HolForm E C) : b3_period E C γ (∑ j ∈ S, θ j) = ∑ j ∈ S, b3_period E C γ (θ j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b3_period, b3_pathPeriod, b3_pathIntegral]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, b3Rest2_period_add, ih]

/-- The real part, as an additive map of `ℂ`. -/
def b3Rest2_gre : ℂ →+ ℂ where
  toFun z := (z.re : ℂ)
  map_zero' := by simp
  map_add' z w := by simp

/-- **`dim H¹(C; ℚ) ≥ 2g`**: the real-part integration cocycles of a real basis of `Ω¹(C)` are
independent over `ℂ` in `H¹(C; ℂ)`. -/
theorem b3Rest2_finrank_cohomology_ge
    [Module.Finite ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1)] :
    2 * Module.finrank ℂ (b3_HolForm E C) ≤
      Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) := by
  obtain ⟨h1, h2, h3⟩ := b3Rest2_lattice_instances (C := C) hE
  obtain ⟨hfin, hrk⟩ := spec_finrank_complexSingular_of_finite_aux (TopCat.of C) 1 inferInstance
  haveI := b3Forms_holForm_finiteDimensional_real (C := C) hE
  obtain ⟨p₀⟩ := (inferInstance : ConnectedSpace C).toNonempty
  obtain ⟨aj, haj⟩ := b3A_exists_abelJacobi hE p₀
  have hajc : Continuous aj := (b3Rest_abelJacobi_holomorphic hE _ aj haj).continuous
  set bR := Module.finBasis ℝ (b3_HolForm E C)
  set x : Fin (Module.finrank ℝ (b3_HolForm E C)) →
      AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of C) 1 := fun j ↦
    Singular.cohomologyClass (TopCat.of C) 1 (b3Rest2_integCocycle aj hajc b3Rest2_gre (bR j))
  have hval : ∀ (j : Fin (Module.finrank ℝ (b3_HolForm E C))) (γ : b3_SmoothLoop E C),
      AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) 1 (x j)
        (((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of C)).sc 1).moduleCatHomologyClass
          (loopCycle ℂ (b3Rest2_circ γ))) = ((b3_period E C γ (bR j)).re : ℂ) := by
    intro j γ
    rw [cohomologyEquivDualHomology_cohomologyClass]
    exact b3Rest2_integCocycle_loop aj hajc hE p₀ haj b3Rest2_gre (bR j) γ (b3Rest2_circ γ)
      (b3Rest2_circ_apply γ)
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
    have hγ : ∀ γ : b3_SmoothLoop E C,
        ∑ j, c j * ((b3_period E C γ (bR j)).re : ℂ) = 0 := by
      intro γ
      let ev : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of C) 1 →ₗ[ℂ] ℂ :=
        (LinearMap.applyₗ (((AlgebraicTopology.Singular.SingularChainComplex ℂ
          (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℂ (b3Rest2_circ γ)))).comp
          (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ (TopCat.of C) 1).toLinearMap
      have hev : ∀ j, ev (x j) = ((b3_period E C γ (bR j)).re : ℂ) := fun j ↦ hval j γ
      have e := congrArg ev hc
      rw [map_sum, map_zero] at e
      simp only [map_smul, smul_eq_mul, hev] at e
      exact e
    have hre : ∀ r : Fin (Module.finrank ℝ (b3_HolForm E C)) → ℝ,
        (∀ γ : b3_SmoothLoop E C, ∑ j, r j * (b3_period E C γ (bR j)).re = 0) → ∀ j, r j = 0 := by
      intro r hr
      have h0 : ∑ j, r j • bR j = 0 := by
        refine b3Rest2_eq_of_re_period hE fun γ ↦ ?_
        rw [b3Rest2_period_sum]
        simp only [b3Rest2_period_rsmul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, hr γ]
        simp [b3_period, b3_pathPeriod, b3_pathIntegral]
      exact Fintype.linearIndependent_iff.1 bR.linearIndependent r h0
    intro j
    apply Complex.ext
    · refine hre (fun j ↦ (c j).re) (fun γ ↦ ?_) j
      have := congrArg Complex.re (hγ γ)
      simpa [Complex.re_sum, Complex.mul_re] using this
    · refine hre (fun j ↦ (c j).im) (fun γ ↦ ?_) j
      have := congrArg Complex.im (hγ γ)
      simpa [Complex.im_sum, Complex.mul_im] using this
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hrk, finrank_real_of_complex] at this
  exact this

/-- **`dim H¹(C; ℚ) = 2g`.** -/
theorem b3Rest2_finrank_cohomology :
    Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of C) 1) =
      2 * Module.finrank ℂ (b3_HolForm E C) := by
  obtain ⟨hfin, hle⟩ := b3Rest2_finrank_cohomology_le (C := C) hE
  exact le_antisymm hle (b3Rest2_finrank_cohomology_ge hE)

end HodgeLean.Foundations.Program

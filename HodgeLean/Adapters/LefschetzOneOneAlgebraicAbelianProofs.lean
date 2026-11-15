import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Convex.Contractible
import HodgeLean.RealDefs.TopDegreeRank
import HodgeLean.Adapters.ThetaExistence

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass
open Filter Set Topology

open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

omit [GrpObj X] in
theorem bh4_cycleComponentSheafClass_mem_span (x : X.left)
    (hx : Order.coheight x = 1) :
    cycleComponentSheafClass X x hx ∈ algebraicCycleClassSpan X 1 := by
  apply le_sSup (s := {Submodule.span ℚ {cycleComponentSheafClass X y hy} |
    (y : X.left) (hy : Order.coheight y = 1)})
  · exact ⟨_, ⟨hx, rfl⟩⟩
  · exact Submodule.subset_span (Set.mem_singleton _)

theorem bh4_theta_nonzero_aux (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 := by
  exact Submodule.exists_mem_ne_zero_of_ne_bot
    (spec_sections_ne_bot (datumOfX X A.H A.E A.integral A.chi A.semicharacter) hpos)

theorem bh4_theta_periodicity_aux (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    θ (z + l) = holFactor (datumOfX X A.H A.E A.integral A.chi A.semicharacter) l z * θ z := by
  exact hθ.2 l z

omit [GrpObj X] [Smooth X.hom] [IsProjective X.hom] in
theorem bh4_theta_nonzero_germ_aux
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : θ ≠ 0)
    (p : Fin (dim X.left) → ℂ) : ¬ ∀ᶠ z in nhds p, θ z = 0 := by
  intro h
  exact hne ((AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn).eq_of_eventuallyEq analyticOnNhd_const h)

theorem bh4_theta_translation_associated_aux (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l : abelianPeriodLattice X) (p : Fin (dim X.left) → ℂ) :
    AreAssociatedAt θ (fun z ↦ θ (z + l)) p := by
  let T := datumOfX X A.H A.E A.integral A.chi A.semicharacter
  refine ⟨fun z ↦ (holFactor T l z)⁻¹, ?_, inv_ne_zero (holFactor_ne_zero T l p), ?_⟩
  · exact (AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn isOpen_univ
      (HodgeLean.Foundations.AutomorphyLineBundle.holFactor_differentiable T l).differentiableOn
      p (mem_univ p)).inv
      (holFactor_ne_zero T l p)
  · exact Eventually.of_forall fun z ↦ by
      change θ z = (holFactor T l z)⁻¹ * θ (z + l)
      rw [bh4_theta_periodicity_aux X A θ hθ l z]
      exact (inv_mul_cancel_left₀ (holFactor_ne_zero T l z) (θ z)).symm

theorem bh4_theta_local_data_aux
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ)
    (hgerm : ∀ p, ¬ ∀ᶠ z in nhds p, θ z = 0)
    (htrans : ∀ (l : abelianPeriodLattice X) p,
      AreAssociatedAt θ (fun z ↦ θ (z + l)) p) :
    ∃ D : bh4_LocalDivisorData X,
      (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) ∧
      localDivisorSupport D.V D.f = {z | θ z = 0} ∧
      abelianExp X '' localDivisorSupport D.V D.f = thetaZeroLocusX X θ := by
  have hassoc : ∀ p, AreAssociatedAt θ θ p := fun _ ↦
    ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun _ ↦ (one_mul _).symm⟩
  let D : bh4_LocalDivisorData X :=
    { ι := Unit
      V := fun _ ↦ univ
      f := fun _ ↦ θ
      valid := ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ (AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn),
        fun _ p _ ↦ hgerm p, fun _ _ p _ ↦ hassoc p⟩
      periodic := fun l _ _ p _ _ ↦ htrans l p }
  have hs : localDivisorSupport D.V D.f = {z | θ z = 0} := by
    ext z
    simp only [localDivisorSupport, D, mem_ofPred_eq, mem_univ, true_and,
      exists_const]
  exact ⟨D, fun _ p _ ↦ hassoc p, hs, by rw [hs]; rfl⟩

theorem bh4_theta_zero_aux (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite)
    (hdim : 0 < dim X.left) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) :
    ∃ z, θ z = 0 := by
  exact bh5_theta_zero_aux X A hpos hdim θ hθ

theorem bh4_theta_divisor_aux (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite) :
    ∃ θ : (Fin (dim X.left) → ℂ) → ℂ,
      θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧ θ ≠ 0 ∧
      ∃ D : bh4_LocalDivisorData X,
        (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p) ∧
        localDivisorSupport D.V D.f = {z | θ z = 0} ∧
        abelianExp X '' localDivisorSupport D.V D.f = thetaZeroLocusX X θ ∧
        (0 < dim X.left → Set.Nonempty (localDivisorSupport D.V D.f)) := by
  obtain ⟨θ, hθ, hne⟩ := bh4_theta_nonzero_aux X A hpos
  obtain ⟨D, hlocal, hs, he⟩ := bh4_theta_local_data_aux X θ hθ.1
    (bh4_theta_nonzero_germ_aux X θ hθ.1 hne)
    (bh4_theta_translation_associated_aux X A θ hθ)
  refine ⟨θ, hθ, hne, D, hlocal, hs, he, ?_⟩
  intro hdim
  rw [hs]
  exact bh4_theta_zero_aux X A hpos hdim θ hθ

theorem bh4_polarization_aux : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite := by
  exact bh5_polarization_aux X

theorem bh4_domination_aux (H H₀ : HermitianForm (V := Fin (dim X.left) → ℂ))
    (hpos : H₀.IsPositiveDefinite) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ v : Fin (dim X.left) → ℂ, v ≠ 0 →
      0 < (H.toFun v v).re + (n : ℝ) * (H₀.toFun v v).re := by
  obtain ⟨c, hc, hc_le⟩ := exists_hermitian_re_lower H₀ hpos
  obtain ⟨N, hN⟩ := exists_nat_gt (‖hermitianCLM H‖ / c)
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  intro n hn v hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hHnorm := hermitian_norm_le H v v
  have hHre : -‖hermitianCLM H‖ * ‖v‖ ^ 2 ≤ (H.toFun v v).re := by
    have hre : -‖H.toFun v v‖ ≤ (H.toFun v v).re := by
      have h := (neg_le_abs (H.toFun v v).re).trans
        (Complex.abs_re_le_norm (H.toFun v v))
      linarith
    calc
      -‖hermitianCLM H‖ * ‖v‖ ^ 2 ≤ -‖H.toFun v v‖ := by
        rw [neg_mul, neg_le_neg_iff]
        simpa only [pow_two, mul_assoc] using hHnorm
      _ ≤ (H.toFun v v).re := hre
  have hnreal : ‖hermitianCLM H‖ / c < (n : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast (Nat.le_of_succ_le hn))
  have hcoef : ‖hermitianCLM H‖ < (n : ℝ) * c := by
    exact (div_lt_iff₀ hc).mp hnreal
  have h₀ := hc_le v
  nlinarith [sq_pos_of_pos hvnorm]

theorem bh4_semicharacter_assembly_aux (A A₀ : bh4_AHData X) (n : ℕ) :
    ∃ P M : bh4_AHData X,
      (∀ v w, P.H.toFun v w = A.H.toFun v w + (n : ℂ) * A₀.H.toFun v w) ∧
      (∀ v w, M.H.toFun v w = (n : ℂ) * A₀.H.toFun v w) ∧
      P.E = A.E + n • A₀.E ∧ M.E = n • A₀.E ∧
      (∀ l, P.chi l = A.chi l * A₀.chi l ^ n) ∧
      (∀ l, M.chi l = A₀.chi l ^ n) := by
  let Hn : HermitianForm (V := Fin (dim X.left) → ℂ) :=
    { toFun := fun v w ↦ (n : ℂ) * A₀.H.toFun v w
      add_left := fun x y z ↦ by rw [A₀.H.add_left]; ring
      smul_left := fun c x y ↦ by rw [A₀.H.smul_left]; ring
      add_right := fun x y z ↦ by rw [A₀.H.add_right]; ring
      smul_right := fun c x y ↦ by rw [A₀.H.smul_right]; ring
      conj_symm := fun x y ↦ by simp [A₀.H.conj_symm] }
  have hHn_imag (v w) : Hn.imaginary v w = (n : ℝ) * A₀.H.imaginary v w := by
    simp only [HermitianForm.imaginary, Hn, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero]
  let M : bh4_AHData X :=
    { H := Hn
      E := n • A₀.E
      integral := fun l m ↦ by
        rw [hHn_imag]
        simp only [AddMonoidHom.smul_apply, nsmul_eq_mul]
        push_cast
        rw [A₀.integral]
      chi := fun l ↦ A₀.chi l ^ n
      semicharacter := fun l m ↦ by
        rw [A₀.semicharacter, mul_pow, mul_pow]
        rw [← Circle.exp_nsmul]
        congr 1
        rw [hHn_imag]
        simp only [nsmul_eq_mul]
        ring }
  let P : bh4_AHData X :=
    { H := A.H.add Hn
      E := A.E + M.E
      integral := fun l m ↦ by
        simp only [AddMonoidHom.add_apply]
        push_cast
        rw [A.integral, M.integral]
        rfl
      chi := fun l ↦ A.chi l * M.chi l
      semicharacter := fun l m ↦ by
        rw [A.semicharacter, M.semicharacter]
        simp only [HermitianForm.imaginary, HermitianForm.add, Complex.add_im,
          mul_add, Circle.exp_add]
        simp only [M]
        ac_rfl }
  refine ⟨P, M, ?_, ?_, ?_, rfl, ?_, fun _ ↦ rfl⟩
  · intro v w
    rfl
  · intro v w
    rfl
  · rfl
  · intro l
    rfl

theorem bh4_positive_difference_aux (A : bh4_AHData X) :
    ∃ P M : bh4_AHData X, P.H.IsPositiveDefinite ∧ M.H.IsPositiveDefinite ∧
      latticeClassHQ X (-A.E) = latticeClassHQ X (-P.E) - latticeClassHQ X (-M.E) := by
  obtain ⟨A₀, h₀⟩ := bh4_polarization_aux X
  obtain ⟨n, hn, hdom⟩ := bh4_domination_aux X A.H A₀.H h₀
  obtain ⟨P, M, hP, hM, hPE, hME, _, _⟩ := bh4_semicharacter_assembly_aux X A A₀ n
  refine ⟨P, M, ?_, ?_, ?_⟩
  · intro v hv
    rw [hP]
    simpa only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] using hdom n le_rfl v hv
  · intro v hv
    rw [hM]
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using mul_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n) (h₀ v hv)
  · rw [hPE, hME, latticeClassHQ_neg, latticeClassHQ_neg, latticeClassHQ_neg,
      spec_latticeClassHQ_add]
    abel

theorem bh4_chern_normalization_aux (A : bh4_AHData X)
    (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE' : ∀ l m, E' l m = chernForm
      (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m) :
    latticeClassHQ X E' = latticeClassHQ X (-A.E) := by
  congr 1
  ext l m
  rw [hE']
  exact spec_chernForm_datumOfX X A.H A.E A.integral A.chi A.semicharacter _
    (spec_holLog_isLog _).1 (spec_holLog_isLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).2 l m

theorem bh4_fundamental_sum_mem_span_aux (D : bh4_LocalDivisorData X)
    (R : bh4_Algebraization X D) :
    (∑ i, (R.mult i : ℚ) •
      forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X (R.x i)) 2
        (cycleComponentSupportedInjectiveClass X (R.x i) (R.codim i))) ∈
      algebraicCycleClassSpan X 1 := by
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (bh4_cycleComponentSheafClass_mem_span X (R.x i) (R.codim i))

private def bh4_latticeEval {Λ : Type*} [AddCommGroup Λ] (l : Λ) :
    Module.Dual ℚ (Λ →+ ℚ) where
  toFun f := f l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem bh4_lattice_pair {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ)
    (hE : ∀ l, E l l = 0) (l m : Λ) :
    Symplectic.contract (latticeClass E) (bh4_latticeEval l) m = (E l m : ℚ) := by
  classical
  have hk (k : Module.Free.ChooseBasisIndex ℤ Λ) :
      Symplectic.contract (latticeClass E) (bh4_latticeEval l)
          (Module.Free.chooseBasis ℤ Λ k) =
        (E l (Module.Free.chooseBasis ℤ Λ k) : ℚ) := by
    rw [contract_latticeClass_apply_of_alt E hE]
    change (∑ i, (latticeDualBasis i l) * _) = _
    conv_rhs => rw [← (Module.Free.chooseBasis ℤ Λ).sum_repr l]
    simp only [map_sum, AddMonoidHom.finsetSum_apply, map_zsmul,
      AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_sum, Int.cast_mul]
    rfl
  conv_lhs => rw [← (Module.Free.chooseBasis ℤ Λ).sum_repr m]
  conv_rhs => rw [← (Module.Free.chooseBasis ℤ Λ).sum_repr m]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_sum, Int.cast_mul, hk, Int.cast_id]

private theorem bh4_exterior_map_map_symm {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (k : ℕ) (z : ⋀[K]^k N) :
    exteriorPower.map k e.toLinearMap (exteriorPower.map k e.symm.toLinearMap z) = z := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  simp

theorem bh4_periodPair_ext_aux (c d : HQ X 2)
    (h : ∀ l m : abelianPeriodLattice X, bh4_periodPair X l m c = bh4_periodPair X l m d) :
    c = d := by
  apply (torusCohomology_cupProductOf X).cupWedgeEquiv 2 |>.symm.injective
  apply exteriorPower.map_injective_field (abelianPeriodEquiv X).injective
  letI : Module.Finite ℚ (abelianPeriodLattice X →+ ℚ) :=
    Module.Finite.of_basis latticeDualBasisQ
  apply Symplectic.contract_injective
  apply latticeDualBasisQ.dualBasis.ext
  intro i
  have he : latticeDualBasisQ.dualBasis i =
      bh4_latticeEval (Module.Free.chooseBasis ℤ (abelianPeriodLattice X) i) := by
    apply latticeDualBasisQ.ext
    intro j
    change latticeDualBasisQ.dualBasis i (latticeDualBasisQ j) =
      (latticeDualBasisQ j) (Module.Free.chooseBasis ℤ (abelianPeriodLattice X) i)
    rw [Module.Basis.dualBasis_apply_self, latticeDualBasisQ_apply,
      latticeDualBasis_apply_basis]
    simp only [eq_comm]
  rw [he]
  ext m
  exact h _ m

theorem bh4_periodPair_lattice_aux (A : bh4_AHData X) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (latticeClassHQ X A.E) = (A.E l m : ℚ) := by
  change Symplectic.contract
    (exteriorPower.map 2 (abelianPeriodEquiv X).toLinearMap
      ((torusCohomology_cupProductOf X).cupWedgeEquiv 2 |>.symm
        (latticeClassHQ X A.E))) (bh4_latticeEval l) m = _
  have hsymm : ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm
      (latticeClassHQ X A.E) =
      exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass A.E) :=
    ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm_apply_apply _
  rw [hsymm]
  rw [bh4_exterior_map_map_symm]
  apply bh4_lattice_pair A.E
  intro x
  have hx := A.integral x x
  have him : A.H.imaginary (x : Fin (dim X.left) → ℂ) x = 0 := by
    have ha := imaginary_antisymm A.H (x : Fin (dim X.left) → ℂ) x
    linarith
  rw [him] at hx
  exact_mod_cast hx

theorem bh4_analytic_set_avoidance_aux
    (Z : Set (Fin (dim X.left) → ℂ))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z) (hproper : Z ≠ univ)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      bh4_squareEdge X l m z i t ∉ Z := by
  exact bh5_analytic_set_avoidance_aux X Z hZ hproper l m

theorem bh4_boundary_avoiding_aux
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : θ ≠ 0)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      θ (bh4_squareEdge X l m z i t) ≠ 0 := by
  apply bh4_analytic_set_avoidance_aux X {z | θ z = 0}
    (AnalyticDivisorAlgebraic2.spec_isClosedAnalytic_zeroSet_of_differentiable hθ)
  intro heq
  apply hne
  funext z
  have hz : z ∈ {z | θ z = 0} := by rw [heq]; exact mem_univ z
  exact hz

theorem bh4_boundary_logs_aux
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Continuous θ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, θ (bh4_squareEdge X l m z i t) ≠ 0) :
    ∃ g : Fin 4 → ℝ → ℂ,
      (∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 →
        θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) := by
  have hedge_cont : ∀ i, Continuous fun t : Icc (0 : ℝ) 1 ↦
      bh4_squareEdge X l m z i t := by
    intro i
    fin_cases i <;> simp only [bh4_squareEdge, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop
  have hlift : ∀ i, ∃ q : Icc (0 : ℝ) 1 → ℂ, Continuous q ∧
      ∀ t, Complex.exp (q t) = θ (bh4_squareEdge X l m z i t) := by
    intro i
    let γ : C(unitInterval, {w : ℂ // w ≠ 0}) :=
      ⟨fun t ↦ ⟨θ (bh4_squareEdge X l m z i t), hnz i t t.property⟩,
        Continuous.subtype_mk (hθ.comp (hedge_cont i)) _⟩
    let e : ℂ := Complex.log (γ 0)
    have he : γ 0 = (⟨Complex.exp e, Complex.exp_ne_zero e⟩ : {w : ℂ // w ≠ 0}) := by
      ext
      exact (Complex.exp_log (γ 0).property).symm
    let q := Complex.isCoveringMap_exp.liftPath γ e he
    refine ⟨q, q.continuous, fun t ↦ ?_⟩
    exact congr_arg Subtype.val (congr_fun
      (Complex.isCoveringMap_exp.liftPath_lifts γ e he) t)
  choose q hq_cont hq_exp using hlift
  refine ⟨fun i t ↦ q i (projIcc 0 1 zero_le_one t) /
      (2 * Real.pi * Complex.I), fun i ↦ ?_, ?_⟩
  · exact ((hq_cont i).comp continuous_projIcc).div_const _ |>.continuousOn
  intro i t ht
  rw [← hq_exp i ⟨t, ht⟩]
  simp only [projIcc_of_mem zero_le_one ht]
  congr 1
  rw [mul_div_cancel₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem bh4_opposite_edge_increments_aux (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    let f := holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)
    ((g 0 1 - g 0 0) + (g 2 1 - g 2 0) = f m z - f m (z + l)) ∧
    ((g 1 1 - g 1 0) + (g 3 1 - g 3 0) = f l (z + m) - f l z) := by
  have hK : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hedge (i : Fin 4) : Continuous fun t : ℝ ↦ bh4_squareEdge X l m z i t := by
    unfold bh4_squareEdge
    fin_cases i <;> simp <;> fun_prop
  have hlift (a b : ℝ → ℂ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
      (hb : ContinuousOn b (Icc (0 : ℝ) 1))
      (he : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp ((2 * Real.pi * Complex.I) * a t) =
        Complex.exp ((2 * Real.pi * Complex.I) * b t)) :
      a 1 - a 0 = b 1 - b 0 := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he 0 ⟨le_rfl, zero_le_one⟩)
    let b' : ℝ → ℂ := fun t ↦ (2 * Real.pi * Complex.I) * b t +
      n * (2 * Real.pi * Complex.I)
    have hb' : ContinuousOn b' (Icc (0 : ℝ) 1) :=
      (continuousOn_const.mul hb).add continuousOn_const
    have he' : (Icc (0 : ℝ) 1).EqOn
        ((fun w : ℂ ↦ (⟨Complex.exp w, Complex.exp_ne_zero w⟩ : {z : ℂ // z ≠ 0})) ∘
          fun t ↦ (2 * Real.pi * Complex.I) * a t)
        ((fun w : ℂ ↦ (⟨Complex.exp w, Complex.exp_ne_zero w⟩ : {z : ℂ // z ≠ 0})) ∘ b') := by
      intro t ht
      apply Subtype.ext
      simp only [Function.comp_apply, b', Complex.exp_add,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
      exact he t ht
    have hzero : (2 * Real.pi * Complex.I) * a 0 = b' 0 := hn
    have hKa : ContinuousOn (fun t ↦ (2 * Real.pi * Complex.I) * a t) (Icc 0 1) :=
      continuousOn_const.mul ha
    have hall := Complex.isCoveringMap_exp.eqOn_of_comp_eqOn
      (ordConnected_Icc.isPreconnected) hKa hb' he'
      ⟨le_rfl, zero_le_one⟩ hzero
    have h0 := hall ⟨le_rfl, zero_le_one⟩
    have h1 := hall ⟨zero_le_one, le_rfl⟩
    dsimp only [b'] at h0 h1
    change (2 * Real.pi * Complex.I) * a 0 =
      (2 * Real.pi * Complex.I) * b 0 + n * (2 * Real.pi * Complex.I) at h0
    change (2 * Real.pi * Complex.I) * a 1 =
      (2 * Real.pi * Complex.I) * b 1 + n * (2 * Real.pi * Complex.I) at h1
    apply (mul_left_cancel₀ hK)
    linear_combination h1 - h0
  have h02exp : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp ((2 * Real.pi * Complex.I) * g 2 (1 - t)) =
        Complex.exp ((2 * Real.pi * Complex.I) * (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter) m
          (z + t • (l : Fin (dim X.left) → ℂ)) + g 0 t)) := by
    intro t ht
    rw [← hexp 2 (1 - t) ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩,
      mul_add, Complex.exp_add, ← hexp 0 t ht, ← (spec_holLog_isLog
        (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).1 m
        (z + t • (l : Fin (dim X.left) → ℂ))]
    rw [show bh4_squareEdge X l m z 2 (1 - t) =
      z + t • (l : Fin (dim X.left) → ℂ) + m by
          change z + (1 - (1 - t)) • (l : Fin (dim X.left) → ℂ) + m = _
          rw [show 1 - (1 - t) = t by ring],
      show bh4_squareEdge X l m z 0 t =
        z + t • (l : Fin (dim X.left) → ℂ) by
          simp [bh4_squareEdge]]
    exact bh4_theta_periodicity_aux X A θ hθ m
      (z + t • (l : Fin (dim X.left) → ℂ))
  have hb02 : ContinuousOn
      (fun t : ℝ ↦ holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter) m
        (z + t • (l : Fin (dim X.left) → ℂ)) + g 0 t) (Icc 0 1) :=
    (((spec_holLog_isLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).2 m).comp
      (hedge 0)).continuousOn.add (hg 0)
  have h02 := hlift (fun t ↦ g 2 (1 - t))
    (fun t ↦ holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter) m
      (z + t • (l : Fin (dim X.left) → ℂ)) + g 0 t)
    ((hg 2).comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht ↦ ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩))
    hb02 h02exp
  have h13exp : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp ((2 * Real.pi * Complex.I) * g 3 (1 - t)) =
        Complex.exp ((2 * Real.pi * Complex.I) * (g 1 t - holLog
          (datumOfX X A.H A.E A.integral A.chi A.semicharacter) l
          (z + t • (m : Fin (dim X.left) → ℂ)))) := by
    intro t ht
    rw [mul_sub, Complex.exp_sub, ← hexp 3 (1 - t)
      ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩, ← hexp 1 t ht,
      ← (spec_holLog_isLog
        (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).1 l
          (z + t • (m : Fin (dim X.left) → ℂ))]
    rw [show bh4_squareEdge X l m z 3 (1 - t) =
        z + t • (m : Fin (dim X.left) → ℂ) by
          simp [bh4_squareEdge],
      show bh4_squareEdge X l m z 1 t =
        z + t • (m : Fin (dim X.left) → ℂ) + l by
          simp only [bh4_squareEdge, Matrix.cons_val_one, Matrix.cons_val_zero]
          abel]
    have hp := bh4_theta_periodicity_aux X A θ hθ l
      (z + t • (m : Fin (dim X.left) → ℂ))
    apply (eq_div_iff (holFactor_ne_zero
      (datumOfX X A.H A.E A.integral A.chi A.semicharacter) l
        (z + t • (m : Fin (dim X.left) → ℂ)))).2
    simpa only [mul_comm] using hp.symm
  have hb13 : ContinuousOn
      (fun t : ℝ ↦ g 1 t - holLog
        (datumOfX X A.H A.E A.integral A.chi A.semicharacter) l
        (z + t • (m : Fin (dim X.left) → ℂ))) (Icc 0 1) :=
    (hg 1).sub (((spec_holLog_isLog
      (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).2 l).comp (by fun_prop)).continuousOn
  have h13 := hlift (fun t ↦ g 3 (1 - t))
    (fun t ↦ g 1 t - holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter) l
      (z + t • (m : Fin (dim X.left) → ℂ)))
    ((hg 3).comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht ↦ ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩))
    hb13 h13exp
  norm_num at h02 h13
  constructor
  · linear_combination -h02
  · linear_combination -h13

theorem bh4_boundary_chern_aux (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryIncrement g =
      -(chernForm (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m : ℂ) := by
  obtain ⟨h02, h13⟩ := bh4_opposite_edge_increments_aux X A θ hθ l m z g hg hexp
  let T := datumOfX X A.H A.E A.integral A.chi A.semicharacter
  have hc := spec_logForm_eq_chernForm (holFactor T) (holLog T)
    (spec_holFactor_cocycle T) (spec_holLog_isLog T).1 (spec_holLog_isLog T).2 z l m
  dsimp only [T] at hc
  rw [← hc]
  unfold bh4_boundaryIncrement logForm
  rw [Fin.sum_univ_four]
  linear_combination h02 + h13

theorem bh4_reduced_cover_equations_aux (D : bh4_LocalDivisorData X)
    (R : bh4_Algebraization X D) :
    ∃ f : Fin R.n → (Fin (dim X.left) → ℂ) → ℂ,
      ∃ hf : ∀ i, AnalyticOnNhd ℂ (f i) univ,
        (∀ i p, Squarefree (⟨Filter.Germ.ofFun (f i), f i, hf i p (mem_univ p), rfl⟩ :
          AnalyticGermAt (dim X.left) p)) ∧
        (∀ i p, f i p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X (R.x i)) ∧
        (∀ j p, p ∈ D.V j →
          AreAssociatedAt (D.f j) (fun z ↦ ∏ i, f i z ^ R.mult i) p) := by
  exact bh5_reduced_cover_equations_aux X D R

theorem bh4_supported_square_evaluation_aux (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hsupport : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    (bh4_periodPair X l m
      (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) 2
        (cycleComponentSupportedInjectiveClass X x hx)) : ℂ) =
      bh4_boundaryWinding X l m z f := by
  exact bh5_supported_square_evaluation_aux X x hx f hf hred hsupport l m z hnz

end HodgeLean.Adapters

private lemma bh4_exp_lift_hasDerivAt {F G : ℝ → ℂ} {t : ℝ}
    (hF : DifferentiableAt ℝ F t) (hG : ContinuousAt G t)
    (heq : ∀ᶠ s in nhds t, Complex.exp (G s) = F s) :
    HasDerivAt G (deriv F t / F t) t := by
  let e := Complex.hasStrictDerivAt_exp (G t)
  have hne : Complex.exp (G t) ≠ 0 := Complex.exp_ne_zero _
  let L := e.localInverse Complex.exp (Complex.exp (G t)) (G t) hne
  have hLG : ∀ᶠ s in nhds t, L (Complex.exp (G s)) = G s :=
    hG.eventually (e.eventually_left_inverse hne)
  have heqt : Complex.exp (G t) = F t := heq.self_of_nhds
  have hLF : HasDerivAt (fun s ↦ L (F s))
      ((Complex.exp (G t))⁻¹ * deriv F t) t := by
    have hL := (HasStrictFDerivAt.hasFDerivAt (e.to_localInverse hne)).restrictScalars ℝ
    have hL' : HasFDerivAt L
        (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (G t))⁻¹)) (F t) := by
      rw [← heqt]
      exact hL
    have hc := hL'.comp t hF.hasFDerivAt
    have hc' : HasDerivAt (L ∘ F) ((Complex.exp (G t))⁻¹ * deriv F t) t := by
      show HasFDerivAt (L ∘ F)
        (ContinuousLinearMap.toSpanSingleton ℝ ((Complex.exp (G t))⁻¹ * deriv F t)) t
      convert hc using 1
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, deriv]
      change x • ((Complex.exp (G t))⁻¹ * (fderiv ℝ F t) 1) =
        (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (G t))⁻¹) ((fderiv ℝ F t) x)
      simp only [ContinuousLinearMap.toSpanSingleton_apply]
      rw [show (fderiv ℝ F t) x = x • (fderiv ℝ F t) 1 by
        rw [← map_smul]; simp]
      simp only [RCLike.real_smul_eq_coe_smul, smul_eq_mul]
      rw [mul_comm (Complex.exp (G t))⁻¹, smul_mul_assoc]
    exact hc'.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  have hcongr : (fun s ↦ L (F s)) =ᶠ[nhds t] G := by
    filter_upwards [heq, hLG] with s hs hs' using hs ▸ hs'
  convert hLF.congr_of_eventuallyEq hcongr.symm using 1 <;>
    simp only [div_eq_inv_mul, ← heqt]

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

private theorem bh4_boundaryWinding_eq_increment
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      f (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryWinding X l m z f = bh4_boundaryIncrement g := by
  let K : ℂ := 2 * Real.pi * Complex.I
  have hK : K ≠ 0 := by simp [K, Real.pi_ne_zero, Complex.I_ne_zero]
  have hedge_diff (i : Fin 4) : Differentiable ℝ (fun t : ℝ ↦
      f (bh4_squareEdge X l m z i t)) := by
    apply hf.restrictScalars ℝ |>.comp
    unfold bh4_squareEdge
    fin_cases i <;> simp <;> fun_prop
  have hedge_cont (i : Fin 4) : Continuous fun t : ℝ ↦
      f (bh4_squareEdge X l m z i t) := (hedge_diff i).continuous
  have hnz (i : Fin 4) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f (bh4_squareEdge X l m z i t) ≠ 0 := by
    rw [hexp i t ht]
    exact Complex.exp_ne_zero _
  have hderiv (i : Fin 4) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (g i)
        (deriv (fun s : ℝ ↦ f (bh4_squareEdge X l m z i s)) t /
          (K * f (bh4_squareEdge X l m z i t))) t := by
    have hgc : ContinuousAt (g i) t :=
      (hg i t ⟨ht.1.le, ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2)
    have he : ∀ᶠ s in nhds t, Complex.exp (K * g i s) =
        f (bh4_squareEdge X l m z i s) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hexp i s ⟨hs.1.le, hs.2.le⟩).symm
    have hd := bh4_exp_lift_hasDerivAt
      (F := fun s : ℝ ↦ f (bh4_squareEdge X l m z i s))
      (G := fun s ↦ K * g i s) (hedge_diff i t) (continuousAt_const.mul hgc) he
    have hd' := hd.div_const K
    have heqg : (fun s ↦ K * g i s / K) = g i := by
      funext s
      exact mul_div_cancel_left₀ (g i s) hK
    rw [heqg] at hd'
    convert hd' using 1
    field_simp
  unfold bh4_boundaryWinding bh4_boundaryIncrement
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (hg i)
    (fun t ht ↦ hderiv i t ht)
  have hcd : Continuous fun t ↦ deriv (fun s : ℝ ↦
      f (bh4_squareEdge X l m z i s)) t := by
    have hec : ContDiff ℝ 1 (bh4_squareEdge X l m z i) := by
      unfold bh4_squareEdge
      fin_cases i <;> simp <;> fun_prop
    have hed : Differentiable ℝ (bh4_squareEdge X l m z i) :=
      hec.differentiable one_ne_zero
    have hedc : Continuous (fun t ↦ deriv (bh4_squareEdge X l m z i) t) :=
      hec.continuous_deriv le_rfl
    have hfc : ContDiff ℂ 1 f := contDiffOn_univ.mp
      ((AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn
        isOpen_univ hf.differentiableOn).contDiffOn uniqueDiffOn_univ)
    have hC : Continuous (fun t ↦ fderiv ℂ f (bh4_squareEdge X l m z i t)
        (deriv (bh4_squareEdge X l m z i) t)) := by
      have hed : Continuous (bh4_squareEdge X l m z i) := by
        unfold bh4_squareEdge
        fin_cases i <;> simp <;> fun_prop
      fun_prop (disch := first | exact hfc.continuous_fderiv one_ne_zero | exact hed.continuous | exact hedc)
    convert hC using 1
    funext t
    have hc := (hf (bh4_squareEdge X l m z i t)).hasFDerivAt.restrictScalars ℝ |>.comp t
      (hed t).hasFDerivAt
    rw [deriv]
    change (fderiv ℝ (f ∘ bh4_squareEdge X l m z i) t) 1 = _
    rw [hc.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    rfl
  have hden : ContinuousOn (fun t ↦ K * f (bh4_squareEdge X l m z i t)) (Icc 0 1) :=
    (continuous_const.mul (hedge_cont i)).continuousOn
  let q : ℝ → ℂ := (fun t ↦ deriv (fun s : ℝ ↦
    f (bh4_squareEdge X l m z i s)) t) / fun t ↦ K * f (bh4_squareEdge X l m z i t)
  change IntervalIntegrable q MeasureTheory.volume 0 1
  have hcq : ContinuousOn q (Icc 0 1) := hcd.continuousOn.div hden
    (fun t ht ↦ mul_ne_zero hK (hnz i t ht))
  have hcq' : ContinuousOn q (uIcc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using hcq
  exact hcq'.intervalIntegrable

theorem bh4_winding_association_aux
    (f h : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hassoc : ∀ p, AreAssociatedAt f h p)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    bh4_boundaryWinding X l m z f = bh4_boundaryWinding X l m z h := by
  classical
  let u : (Fin (dim X.left) → ℂ) → (Fin (dim X.left) → ℂ) → ℂ :=
    fun p ↦ (hassoc p).choose
  have hu (p) : AnalyticAt ℂ (u p) p := (hassoc p).choose_spec.1
  have hu0 (p) : u p p ≠ 0 := (hassoc p).choose_spec.2.1
  have hfu (p) : f =ᶠ[nhds p] fun q ↦ u p q * h q :=
    (hassoc p).choose_spec.2.2
  have hhne : h ≠ 0 := by
    intro heq
    have hf0 := hnz 0 0 ⟨le_rfl, zero_le_one⟩
    obtain ⟨v, _, _, hv⟩ := hassoc (bh4_squareEdge X l m z 0 0)
    apply hf0
    rw [hv.self_of_nhds, heq]
    exact mul_zero _
  let U : (Fin (dim X.left) → ℂ) → ℂ := fun p ↦
    if hp : h p ≠ 0 then f p / h p else u p p
  have hUeq (p) : U =ᶠ[nhds p] u p := by
    have hboth : ∀ᶠ q in nhds p, AnalyticAt ℂ (u p) q ∧
        f q = u p q * h q := (AnalyticAt.eventually_analyticAt (hu p)).and (hfu p)
    change {q | AnalyticAt ℂ (u p) q ∧ f q = u p q * h q} ∈ nhds p at hboth
    rw [mem_nhds_iff] at hboth
    obtain ⟨O, hOsub, hOopen, hpO⟩ := hboth
    filter_upwards [hOopen.mem_nhds hpO] with q hqO
    have hqa := (hOsub hqO).1
    have hqrel := (hOsub hqO).2
    by_cases hq : h q ≠ 0
    · simp only [U, dif_pos hq]
      exact (div_eq_iff hq).2 hqrel
    · simp only [U, dif_neg hq]
      by_contra hneq
      have hzero : ∀ᶠ r in nhds q, h r = 0 := by
        have hdiff : ∀ᶠ r in nhds q, u q r - u p r ≠ 0 :=
          ((hu q).continuousAt.sub hqa.continuousAt).eventually_ne (sub_ne_zero.mpr hneq)
        filter_upwards [hfu q, hOopen.mem_nhds hqO, hdiff] with r hqr hrO hne
        have hpr := (hOsub hrO).2
        apply (mul_eq_zero.mp ?_).resolve_left hne
        calc
          (u q r - u p r) * h r = u q r * h r - u p r * h r := by ring
          _ = 0 := by rw [← hqr, ← hpr, sub_self]
      exact bh4_theta_nonzero_germ_aux X h hh hhne q hzero
  have hUa : ∀ p, AnalyticAt ℂ U p := by
    intro p
    rw [← analyticWithinAt_univ]
    exact AnalyticWithinAt.congr_of_eventuallyEq (hu p).analyticWithinAt
      (by simpa only [nhdsWithin_univ] using hUeq p) (hUeq p).self_of_nhds
  have hUd : Differentiable ℂ U := fun p ↦ (hUa p).differentiableAt
  have hU0 (p) : U p ≠ 0 := by
    rw [(hUeq p).self_of_nhds]
    exact hu0 p
  have hf_eq : f = fun p ↦ U p * h p := by
    funext p
    rw [(hUeq p).self_of_nhds]
    exact (hfu p).self_of_nhds
  have hhnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      h (bh4_squareEdge X l m z i t) ≠ 0 := by
    intro i t ht hzero
    apply hnz i t ht
    rw [congrFun hf_eq (bh4_squareEdge X l m z i t)]
    rw [hzero, mul_zero]
  let hcontract : ContractibleSpace (univ : Set (Fin (dim X.left) → ℂ)) :=
    convex_univ.contractibleSpace
    (Set.univ_nonempty : (univ : Set (Fin (dim X.left) → ℂ)).Nonempty)
  letI : ContractibleSpace (univ : Set (Fin (dim X.left) → ℂ)) := hcontract
  obtain ⟨G, hGc, hGexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (U := (univ : Set (Fin (dim X.left) → ℂ))) (by
      show SimplyConnectedSpace (univ : Set (Fin (dim X.left) → ℂ))
      infer_instance) isOpen_univ
    hUd.continuous.continuousOn (by simpa only [image_univ, mem_range, not_exists] using hU0)
  let K : ℂ := 2 * Real.pi * Complex.I
  have hK : K ≠ 0 := by simp [K, Real.pi_ne_zero, Complex.I_ne_zero]
  let gU : Fin 4 → ℝ → ℂ := fun i t ↦ G (bh4_squareEdge X l m z i t) / K
  have hgUc : ∀ i, ContinuousOn (gU i) (Icc (0 : ℝ) 1) := by
    intro i
    have hed : Continuous (bh4_squareEdge X l m z i) := by
      unfold bh4_squareEdge
      fin_cases i <;> simp <;> fun_prop
    apply Continuous.continuousOn
    exact ((continuousOn_univ.mp hGc).comp hed).div_const K
  have hgUexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      U (bh4_squareEdge X l m z i t) = Complex.exp (K * gU i t) := by
    intro i t _
    rw [show K * gU i t = G (bh4_squareEdge X l m z i t) by
      simp only [gU]; field_simp]
    exact (hGexp (mem_univ _)).symm
  have hwindU := bh4_boundaryWinding_eq_increment X U hUd l m z gU hgUc (by
    simpa only [K] using hgUexp)
  have hincU : bh4_boundaryIncrement gU = 0 := by
    unfold bh4_boundaryIncrement
    rw [Fin.sum_univ_four]
    simp [gU, bh4_squareEdge]
  obtain ⟨gH, hgHc, hgHexp⟩ := bh4_boundary_logs_aux X h hh.continuous l m z hhnz
  let gF : Fin 4 → ℝ → ℂ := fun i t ↦ gU i t + gH i t
  have hgFc : ∀ i, ContinuousOn (gF i) (Icc (0 : ℝ) 1) :=
    fun i ↦ (hgUc i).add (hgHc i)
  have hgFexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      f (bh4_squareEdge X l m z i t) = Complex.exp (K * gF i t) := by
    intro i t ht
    rw [congrFun hf_eq (bh4_squareEdge X l m z i t)]
    rw [hgUexp i t ht, hgHexp i t ht]
    simp only [gF, K, mul_add, Complex.exp_add]
  rw [bh4_boundaryWinding_eq_increment X f hf l m z gF hgFc (by
      simpa only [K] using hgFexp),
    bh4_boundaryWinding_eq_increment X h hh l m z gH hgHc hgHexp]
  unfold bh4_boundaryIncrement gF
  rw [show (∑ i, (gU i 1 + gH i 1 - (gU i 0 + gH i 0))) =
      bh4_boundaryIncrement gU + bh4_boundaryIncrement gH by
    unfold bh4_boundaryIncrement
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [hincU, zero_add]
  rfl

theorem bh4_winding_multiplicities_aux (n : ℕ)
    (f : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
    (hf : ∀ j, Differentiable ℂ (f j)) (mult : Fin n → ℕ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ j i, ∀ t ∈ Icc (0 : ℝ) 1, f j (bh4_squareEdge X l m z i t) ≠ 0) :
    bh4_boundaryWinding X l m z (fun p ↦ ∏ j, f j p ^ mult j) =
      ∑ j, (mult j : ℂ) * bh4_boundaryWinding X l m z (f j) := by
  classical
  have hlogs (j : Fin n) := bh4_boundary_logs_aux X (f j) (hf j).continuous
    l m z (hnz j)
  let g : Fin n → Fin 4 → ℝ → ℂ := fun j ↦ (hlogs j).choose
  have hg (j : Fin n) : ∀ i, ContinuousOn (g j i) (Icc (0 : ℝ) 1) :=
    (hlogs j).choose_spec.1
  have hexp (j : Fin n) : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      f j (bh4_squareEdge X l m z i t) =
        Complex.exp (2 * Real.pi * Complex.I * g j i t) :=
    (hlogs j).choose_spec.2
  let G : Fin 4 → ℝ → ℂ := fun i t ↦ ∑ j, (mult j : ℂ) * g j i t
  have hGc : ∀ i, ContinuousOn (G i) (Icc (0 : ℝ) 1) := by
    intro i
    exact continuousOn_finset_sum _ fun j _ ↦ continuousOn_const.mul (hg j i)
  have hGexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      (∏ j, f j (bh4_squareEdge X l m z i t) ^ mult j) =
        Complex.exp (2 * Real.pi * Complex.I * G i t) := by
    intro i t ht
    rw [show 2 * Real.pi * Complex.I * G i t =
        ∑ j, (mult j : ℂ) * (2 * Real.pi * Complex.I * g j i t) by
      simp only [G, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [hexp j i t ht]
    rw [← Complex.exp_nat_mul]
  have hprod : Differentiable ℂ (fun p ↦ ∏ j, f j p ^ mult j) := by
    fun_prop
  rw [bh4_boundaryWinding_eq_increment X _ hprod l m z G hGc hGexp]
  simp_rw [bh4_boundaryWinding_eq_increment X (f _) (hf _) l m z (g _) (hg _) (hexp _)]
  unfold bh4_boundaryIncrement G
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bh4_winding_orientation_aux
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      f (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryWinding X l m z f = bh4_boundaryIncrement g := by
  exact bh4_boundaryWinding_eq_increment X f hf l m z g hg hexp

theorem bh4_boundary_fundamental_aux
    (θ : (Fin (dim X.left) → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : θ ≠ 0)
    (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    (bh4_periodPair X l m
      (∑ i, (R.mult i : ℚ) •
        forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X (R.x i)) 2
          (cycleComponentSupportedInjectiveClass X (R.x i) (R.codim i))) : ℂ) =
      bh4_boundaryIncrement g := by
  classical
  obtain ⟨f, hf, hred, hs, hprod⟩ := bh4_reduced_cover_equations_aux X D R
  have hfd : ∀ i, Differentiable ℂ (f i) := fun i p ↦ (hf i p (mem_univ p)).differentiableAt
  let F : (Fin (dim X.left) → ℂ) → ℂ := fun p ↦ ∏ i, f i p ^ R.mult i
  have hFd : Differentiable ℂ F := by
    intro p
    exact (Finset.analyticAt_fun_prod _ fun i _ ↦
      (hf i p (mem_univ p)).pow (R.mult i)).differentiableAt
  have ha : ∀ p, AreAssociatedAt θ F p := by
    intro p
    have hp : p ∈ ⋃ j, D.V j := by rw [D.valid.2.1]; exact mem_univ p
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    obtain ⟨u, hu, hu0, hueq⟩ := hlocal j p hj
    obtain ⟨v, hv, hv0, hveq⟩ := hprod j p hj
    refine ⟨fun q ↦ (u q)⁻¹ * v q, (hu.inv hu0).mul hv,
      mul_ne_zero (inv_ne_zero hu0) hv0, ?_⟩
    filter_upwards [hueq, hveq, hu.continuousAt.eventually_ne hu0] with q hq hq' huq
    change θ q = (u q)⁻¹ * v q * F q
    rw [mul_assoc, ← hq', hq]
    exact (inv_mul_cancel_left₀ huq (θ q)).symm
  have hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      θ (bh4_squareEdge X l m z i t) ≠ 0 := by
    intro i t ht
    rw [hexp i t ht]
    exact Complex.exp_ne_zero _
  have hfnz : ∀ j i, ∀ t ∈ Icc (0 : ℝ) 1,
      f j (bh4_squareEdge X l m z i t) ≠ 0 := by
    intro j i t ht hj
    obtain ⟨u, _, _, hu⟩ := ha (bh4_squareEdge X l m z i t)
    have hFzero : F (bh4_squareEdge X l m z i t) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hj, zero_pow (Nat.ne_of_gt (R.positive j))]
    apply hnz i t ht
    calc
      θ (bh4_squareEdge X l m z i t) =
          u (bh4_squareEdge X l m z i t) * F (bh4_squareEdge X l m z i t) :=
        hu.self_of_nhds
      _ = 0 := by rw [hFzero, mul_zero]
  calc
    _ = ∑ i, (R.mult i : ℂ) * bh4_boundaryWinding X l m z (f i) := by
      let C : Fin R.n → HQ X 2 := fun i ↦
        cycleComponentSheafClass X (R.x i) (R.codim i)
      change ((bh4_periodPair X l m) (∑ i, (R.mult i : ℚ) • C i) : ℂ) = _
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro i _
      have heval : (bh4_periodPair X l m (C i) : ℂ) =
          bh4_boundaryWinding X l m z (f i) :=
        bh4_supported_square_evaluation_aux X (R.x i) (R.codim i) (f i) (hf i)
          (hred i) (hs i) l m z (hfnz i)
      rw [heval]
    _ = bh4_boundaryWinding X l m z F :=
      (bh4_winding_multiplicities_aux X R.n f hfd R.mult l m z hfnz).symm
    _ = bh4_boundaryWinding X l m z θ :=
      (bh4_winding_association_aux X θ F hθ hFd ha l m z hnz).symm
    _ = _ := bh4_winding_orientation_aux X θ hθ l m z g hg hexp

theorem bh4_theta_divisor_period_aux (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hne : θ ≠ 0) (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m
      (∑ i, (R.mult i : ℚ) •
        forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X (R.x i)) 2
          (cycleComponentSupportedInjectiveClass X (R.x i) (R.codim i))) =
      -(chernForm (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m : ℚ) := by
  obtain ⟨z, hnz⟩ := bh4_boundary_avoiding_aux X θ hθ.1 hne l m
  obtain ⟨g, hg, hexp⟩ := bh4_boundary_logs_aux X θ hθ.1.continuous l m z hnz
  have hf := bh4_boundary_fundamental_aux X θ hθ.1 hne D hlocal R l m z g hg hexp
  have hc := bh4_boundary_chern_aux X A θ hθ l m z g hg hexp
  exact_mod_cast hf.trans hc

theorem bh4_chern_comparison_aux (A : bh4_AHData X)
    (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : θ ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter))
    (hne : θ ≠ 0) (D : bh4_LocalDivisorData X)
    (hlocal : ∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) θ p)
    (R : bh4_Algebraization X D) :
    latticeClassHQ X (-A.E) =
      -∑ i, (R.mult i : ℚ) • cycleComponentSheafClass X (R.x i) (R.codim i) := by
  apply bh4_periodPair_ext_aux X
  intro l m
  have hdiv := bh4_theta_divisor_period_aux X A θ hθ hne D hlocal R l m
  change bh4_periodPair X l m
    (∑ i, (R.mult i : ℚ) • cycleComponentSheafClass X (R.x i) (R.codim i)) = _ at hdiv
  have hsign := spec_chernForm_datumOfX X A.H A.E A.integral A.chi A.semicharacter _
    (spec_holLog_isLog _).1
    (spec_holLog_isLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)).2 l m
  let S : HQ X 2 := ∑ i, (R.mult i : ℚ) • cycleComponentSheafClass X (R.x i) (R.codim i)
  change bh4_periodPair X l m (latticeClassHQ X (-A.E)) = bh4_periodPair X l m (-S)
  change bh4_periodPair X l m S = _ at hdiv
  have hsignQ : (chernForm
      (holLog (datumOfX X A.H A.E A.integral A.chi A.semicharacter)) l m : ℚ) =
      -(A.E l m : ℚ) := by
    exact_mod_cast hsign
  rw [latticeClassHQ_neg, map_neg, bh4_periodPair_lattice_aux, map_neg, hdiv]
  simpa only [neg_neg] using hsignQ.symm

theorem bh4_positive_chern_mem_span (hG : bh4_LocalDivisorDataAlgebraizes X)
    (A : bh4_AHData X) (hpos : A.H.IsPositiveDefinite) :
    latticeClassHQ X (-A.E) ∈ algebraicCycleClassSpan X 1 := by
  obtain ⟨θ, hθ, hne, D, hlocal, _, _⟩ := bh4_theta_divisor_aux X A hpos
  obtain ⟨R⟩ := hG D
  rw [bh4_chern_comparison_aux X A θ hθ hne D hlocal R]
  apply Submodule.neg_mem
  exact bh4_fundamental_sum_mem_span_aux X D R

theorem bh4_chern_mem_span (hG : bh4_LocalDivisorDataAlgebraizes X)
    (A : bh4_AHData X) :
    latticeClassHQ X (-A.E) ∈ algebraicCycleClassSpan X 1 := by
  obtain ⟨P, M, hP, hM, heq⟩ := bh4_positive_difference_aux X A
  rw [heq]
  exact Submodule.sub_mem _ (bh4_positive_chern_mem_span X hG P hP)
    (bh4_positive_chern_mem_span X hG M hM)

theorem bh4_lefschetzOneOneFor_of_localDivisorDataAlgebraizes
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (hG : bh4_LocalDivisorDataAlgebraizes X) : LefschetzOneOneFor X := by
  rw [spec_lefschetzOneOneFor_iff_appellHumbert_chernClassHQ X hF hBdR]
  intro E B hB hEalt h11
  obtain ⟨H, hE, _, _, chi, hchi, E', hE', hclass⟩ :=
    spec_exists_chernClassHQ_of_riemann X E B hB hEalt h11
  refine ⟨H, hE, chi, hchi, E', hE', hclass, ?_⟩
  rw [hclass, ← latticeClassHQ_neg]
  exact bh4_chern_mem_span X hG ⟨H, E, hE, chi, hchi⟩

-- Degenerate unit-divisor check; this is not the positive-dimensional theta witness.
theorem bh4_trivial_theta_witness :
    ∃ A : bh4_AHData X, A.H = HermitianForm.zero ∧
      (fun _ ↦ (1 : ℂ)) ∈ sections (datumOfX X A.H A.E A.integral A.chi A.semicharacter) ∧
      ∃ D : bh4_LocalDivisorData X, Nonempty (bh4_Algebraization X D) ∧
        (∀ i p, p ∈ D.V i → AreAssociatedAt (D.f i) (fun _ ↦ 1) p) := by
  let A : bh4_AHData X :=
    { H := HermitianForm.zero
      E := 0
      integral := by intros; simp [HermitianForm.imaginary, HermitianForm.zero]
      chi := fun _ ↦ 1
      semicharacter := by intros; simp [HermitianForm.imaginary, HermitianForm.zero] }
  have hassoc : ∀ p : Fin (dim X.left) → ℂ,
      AreAssociatedAt (fun _ ↦ (1 : ℂ)) (fun _ ↦ 1) p := fun _ ↦
    ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun _ ↦ (one_mul _).symm⟩
  let D : bh4_LocalDivisorData X :=
    { ι := Unit
      V := fun _ ↦ univ
      f := fun _ _ ↦ 1
      valid := ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ analyticOnNhd_const,
        fun _ _ _ h ↦ one_ne_zero h.self_of_nhds, fun _ _ p _ ↦ hassoc p⟩
      periodic := fun _ _ _ p _ _ ↦ hassoc p }
  refine ⟨A, rfl, ⟨differentiable_const 1, ?_⟩, D, ⟨?_⟩, fun _ p _ ↦ hassoc p⟩
  · intro l z
    simp [holFactor, datumOfX, A, HermitianForm.zero]
  · refine { n := 0, x := Fin.elim0, distinct := ?_, codim := fun i ↦ i.elim0,
             mult := Fin.elim0, positive := fun i ↦ i.elim0, support := ?_, local_equations := ?_ }
    · intro i
      exact i.elim0
    · simp [localDivisorSupport, D]
    · intro j p hp
      refine ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
        fun i ↦ i.elim0, ?_⟩
      simpa only [Finset.univ_eq_empty, Finset.prod_empty] using hassoc p

end HodgeLean.Adapters

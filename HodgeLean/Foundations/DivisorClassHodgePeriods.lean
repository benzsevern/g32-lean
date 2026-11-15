import HodgeLean.Foundations.DivisorClassHodgeDefs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian
import HodgeLean.Foundations.AutomorphyChernClass

/-! # Divisor classes on abelian varieties: periods of lattice classes and boundary increments

Helpers for the period computation of the DC1 route (sub-stage g):

* `dcp_periodPair_latticeClassHQ`: the period pair of `latticeClassHQ X E` at `(l, m)` is
  `E l m` for every alternating integral `E` (the argument of `spec_bh4_periodPair_lattice`,
  which uses only that `E` is alternating);
* `dcp_boundary_chern`: the four boundary increments of continuous logarithms of a section of an
  arbitrary factor with a continuous logarithm sum to `-chernForm` (the argument of
  `spec_bh4_opposite_edge_increments` and `spec_bh4_boundary_chern` with the factor as a binder).

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Filter Set Topology

namespace HodgeLean.Foundations

section Lattice

private def dcp_latticeEval {Λ : Type*} [AddCommGroup Λ] (l : Λ) :
    Module.Dual ℚ (Λ →+ ℚ) where
  toFun f := f l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem dcp_lattice_pair {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ)
    (hE : ∀ l, E l l = 0) (l m : Λ) :
    Symplectic.contract (latticeClass E) (dcp_latticeEval l) m = (E l m : ℚ) := by
  classical
  have hk (k : Module.Free.ChooseBasisIndex ℤ Λ) :
      Symplectic.contract (latticeClass E) (dcp_latticeEval l)
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

private theorem dcp_exterior_map_map_symm {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (k : ℕ) (z : ⋀[K]^k N) :
    exteriorPower.map k e.toLinearMap (exteriorPower.map k e.symm.toLinearMap z) = z := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  simp

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- The period pair of the class of an alternating integral form is its value.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.3 and Lemma 1.3.1;
`spec_bh4_periodPair_lattice`. -/
theorem dcp_periodPair_latticeClassHQ
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l : abelianPeriodLattice X, E l l = 0) (l m : abelianPeriodLattice X) :
    bh4_periodPair X l m (latticeClassHQ X E) = (E l m : ℚ) := by
  change Symplectic.contract
    (exteriorPower.map 2 (abelianPeriodEquiv X).toLinearMap
      ((torusCohomology_cupProductOf X).cupWedgeEquiv 2 |>.symm
        (latticeClassHQ X E))) (dcp_latticeEval l) m = _
  have hsymm : ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm
      (latticeClassHQ X E) =
      exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass E) :=
    ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm_apply_apply _
  rw [hsymm, dcp_exterior_map_map_symm]
  exact dcp_lattice_pair E hE l m

end Lattice

section Boundary

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- Two continuous functions on `[0, 1]` with the same exponential `exp (2πi ·)` have the same
increment.
Source: Hatcher, *Algebraic Topology*, §1.3 (uniqueness of lifts to a covering space). -/
theorem dcp_increment_eq_of_exp_eq (a b : ℝ → ℂ) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hb : ContinuousOn b (Icc (0 : ℝ) 1))
    (he : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp ((2 * Real.pi * Complex.I) * a t) =
      Complex.exp ((2 * Real.pi * Complex.I) * b t)) :
    a 1 - a 0 = b 1 - b 0 := by
  have hK : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
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

/-- Opposite edges of the period square, for a section `θ` of an arbitrary factor `a` with a
continuous logarithm `F`: their increments differ by values of `F`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and Theorem 2.1.2;
`spec_bh4_opposite_edge_increments`. -/
theorem dcp_opposite_edge_increments
    (a F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : ∀ (l : abelianPeriodLattice X) z, θ (z + l) = a l z * θ z)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    ((g 0 1 - g 0 0) + (g 2 1 - g 2 0) = F m z - F m (z + l)) ∧
    ((g 1 1 - g 1 0) + (g 3 1 - g 3 0) = F l (z + m) - F l z) := by
  have hedge (i : Fin 4) : Continuous fun t : ℝ ↦ bh4_squareEdge X l m z i t := by
    unfold bh4_squareEdge
    fin_cases i <;> simp <;> fun_prop
  have h02exp : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp ((2 * Real.pi * Complex.I) * g 2 (1 - t)) =
        Complex.exp ((2 * Real.pi * Complex.I) *
          (F m (z + t • (l : Fin (dim X.left) → ℂ)) + g 0 t)) := by
    intro t ht
    rw [← hexp 2 (1 - t) ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩,
      mul_add, Complex.exp_add, ← hexp 0 t ht, ← hlog m
        (z + t • (l : Fin (dim X.left) → ℂ))]
    rw [show bh4_squareEdge X l m z 2 (1 - t) =
      z + t • (l : Fin (dim X.left) → ℂ) + m by
          change z + (1 - (1 - t)) • (l : Fin (dim X.left) → ℂ) + m = _
          rw [show 1 - (1 - t) = t by ring],
      show bh4_squareEdge X l m z 0 t =
        z + t • (l : Fin (dim X.left) → ℂ) by
          simp [bh4_squareEdge]]
    exact hθ m (z + t • (l : Fin (dim X.left) → ℂ))
  have hb02 : ContinuousOn
      (fun t : ℝ ↦ F m (z + t • (l : Fin (dim X.left) → ℂ)) + g 0 t) (Icc 0 1) :=
    ((hF m).comp (hedge 0)).continuousOn.add (hg 0)
  have h02 := dcp_increment_eq_of_exp_eq (fun t ↦ g 2 (1 - t))
    (fun t ↦ F m (z + t • (l : Fin (dim X.left) → ℂ)) + g 0 t)
    ((hg 2).comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht ↦ ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩))
    hb02 h02exp
  have h13exp : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp ((2 * Real.pi * Complex.I) * g 3 (1 - t)) =
        Complex.exp ((2 * Real.pi * Complex.I) *
          (g 1 t - F l (z + t • (m : Fin (dim X.left) → ℂ)))) := by
    intro t ht
    rw [mul_sub, Complex.exp_sub, ← hexp 3 (1 - t)
      ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩, ← hexp 1 t ht,
      ← hlog l (z + t • (m : Fin (dim X.left) → ℂ))]
    rw [show bh4_squareEdge X l m z 3 (1 - t) =
        z + t • (m : Fin (dim X.left) → ℂ) by
          simp [bh4_squareEdge],
      show bh4_squareEdge X l m z 1 t =
        z + t • (m : Fin (dim X.left) → ℂ) + l by
          simp only [bh4_squareEdge, Matrix.cons_val_one, Matrix.cons_val_zero]
          abel]
    have hp := hθ l (z + t • (m : Fin (dim X.left) → ℂ))
    have ha0 : a l (z + t • (m : Fin (dim X.left) → ℂ)) ≠ 0 := by
      rw [hlog]; exact Complex.exp_ne_zero _
    apply (eq_div_iff ha0).2
    simpa only [mul_comm] using hp.symm
  have hb13 : ContinuousOn
      (fun t : ℝ ↦ g 1 t - F l (z + t • (m : Fin (dim X.left) → ℂ))) (Icc 0 1) :=
    (hg 1).sub ((hF l).comp (by fun_prop)).continuousOn
  have h13 := dcp_increment_eq_of_exp_eq (fun t ↦ g 3 (1 - t))
    (fun t ↦ g 1 t - F l (z + t • (m : Fin (dim X.left) → ℂ)))
    ((hg 3).comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht ↦ ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩))
    hb13 h13exp
  norm_num at h02 h13
  constructor
  · linear_combination -h02
  · linear_combination -h13

/-- The boundary increments of a section of an arbitrary factor sum to `-chernForm`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 and Theorem 2.1.2;
`spec_bh4_boundary_chern`, `spec_logForm_eq_chernForm`. -/
theorem dcp_boundary_chern (a F : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (hcoc : ∀ (l m : abelianPeriodLattice X) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l)) (θ : (Fin (dim X.left) → ℂ) → ℂ)
    (hθ : ∀ (l : abelianPeriodLattice X) z, θ (z + l) = a l z * θ z)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (g : Fin 4 → ℝ → ℂ) (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hexp : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
      θ (bh4_squareEdge X l m z i t) = Complex.exp (2 * Real.pi * Complex.I * g i t)) :
    bh4_boundaryIncrement g = -(chernForm F l m : ℂ) := by
  obtain ⟨h02, h13⟩ := dcp_opposite_edge_increments X a F hlog hF θ hθ l m z g hg hexp
  have hc := spec_logForm_eq_chernForm a F hcoc hlog hF z l m
  rw [← hc]
  unfold bh4_boundaryIncrement logForm
  rw [Fin.sum_univ_four]
  linear_combination h02 + h13

end Boundary

section Cover

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- The cover divisor is invariant under the period lattice, so an equation of it has an
invariant zero set.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `abelianExp_add_lattice`. -/
theorem dcp_zero_periodic (x : X.left) (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hzero : ∀ p, f p = 0 ↔ p ∈ dc1_coverDivisor X x) (l : abelianPeriodLattice X)
    (p : Fin (dim X.left) → ℂ) : f (p + l) = 0 ↔ f p = 0 := by
  rw [hzero, hzero]
  change abelianExp X (p + l) ∈ bh4_componentSupport X x ↔
    abelianExp X p ∈ bh4_componentSupport X x
  rw [abelianExp_add_lattice]

/-- A function with a squarefree germ at some point is not identically zero.
Source: unique factorization of germs (`Squarefree.ne_zero`). -/
theorem dcp_ne_zero_of_squarefree {n : ℕ} (f : (Fin n → ℂ) → ℂ) (p : Fin n → ℂ)
    (hf : AnalyticAt ℂ f p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p)) : f ≠ 0 := by
  rintro rfl
  apply hred.ne_zero
  rfl

end Cover

end HodgeLean.Foundations

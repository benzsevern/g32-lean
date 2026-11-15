import HodgeLean.Foundations.AnalyticStratification
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8CurvatureProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelianDefs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5SegmentProofs
import HodgeLean.Adapters.RiemannFormHermitian

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open Set Filter Topology Metric
open scoped ENNReal
namespace HodgeLean.Adapters

/-- The projectivity bridge, before Hermitian reconstruction and semicharacters.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, second edition, section 4.3,
Riemann's projectivity criterion. -/
theorem bh5_projective_riemann_form_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l, E l l = 0) ∧ (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ (∀ v, v ≠ 0 → 0 < B v (Complex.I • v)) := by
  exact bh8_projective_riemann_form_aux X

/-- Reconstruct the positive datum from the projective Riemann form.
Source: `spec_exists_datumOfX_of_riemann`; Birkenhake--Lange, Lemma 1.3.1. -/
theorem bh5_polarization_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : ∃ A₀ : bh4_AHData X, A₀.H.IsPositiveDefinite := by
  obtain ⟨E, B, hE, hB, h11, hp⟩ := bh5_projective_riemann_form_aux X
  obtain ⟨H, hi, hHB, chi, hc, _⟩ := spec_exists_datumOfX_of_riemann X E hE B hB h11
  refine ⟨⟨H, E, hi, chi, hc⟩, ?_⟩
  intro v hv
  have he : (H.toFun v v).re = B v (Complex.I • v) := by
    rw [spec_hermitian_toFun_eq_imaginary H v v]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, hHB]
  exact he.symm ▸ hp v hv

/-- The image of a differentiable complex chart has at most its real parameter dimension.
This applies separately to each regular stratum chart.
Source: `DifferentiableOn.dimH_image_le` and `Real.dimH_univ_eq_finrank`. -/
theorem bh5_regular_chart_dim (n d : ℕ) (U : Set (Fin d → ℂ))
    (f : (Fin d → ℂ) → (Fin n → ℂ)) (hf : DifferentiableOn ℂ f U) :
    dimH (f '' U) ≤ (2 * d : ℕ) := by
  calc
    dimH (f '' U) ≤ dimH U := hf.dimH_image_le
    _ ≤ dimH (univ : Set (Fin d → ℂ)) := dimH_mono (subset_univ U)
    _ = (2 * d : ℕ) := by
      rw [Real.dimH_univ_eq_finrank, Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex, Nat.mul_comm]

/-- Countably many charts of the regular strata cover a proper analytic subset.
The parameter dimensions are strictly below the ambient complex dimension; singular strata
are covered as well. Empty chart domains allow an empty analytic set.
Source: Gunning--Rossi, Chapter III, regular loci and stratification by complex dimension. -/
theorem bh5_analytic_stratification_aux (n : ℕ) (hn : 0 < n)
    (Z : Set (Fin n → ℂ)) (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (f : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, d j < n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (f j) (U j)) ∧ Z = ⋃ j, f j '' U j := by
  exact astrat_analytic_stratification n hn Z hZ hp

/-- Countable chart images inherit a uniform Hausdorff bound.
Source: `Metric.dimH_iUnion`; monotonicity of Hausdorff dimension. -/
theorem bh5_countable_chart_bound (n : ℕ) (Z : Set (Fin n → ℂ))
    (S : ℕ → Set (Fin n → ℂ)) (hcover : Z = ⋃ j, S j)
    (b : ℝ≥0∞) (hS : ∀ j, dimH (S j) ≤ b) : dimH Z ≤ b := by
  rw [hcover, dimH_iUnion]
  exact iSup_le hS

/-- A proper analytic subset of positive-dimensional complex affine space has real
Hausdorff dimension at most twice the complex dimension minus two.
Source: Gunning--Rossi, Chapter III, dimension and regular loci of analytic sets. -/
theorem bh5_analytic_dim_aux (n : ℕ) (hn : 0 < n) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    dimH Z ≤ (2 * n - 2 : ℕ) := by
  obtain ⟨d, U, f, hd, _, hf, hcover⟩ := bh5_analytic_stratification_aux n hn Z hZ hp
  apply bh5_countable_chart_bound n Z (fun j ↦ f j '' U j) hcover
  intro j
  exact (bh5_regular_chart_dim n (d j) (U j) (f j) (hf j)).trans
    (by exact_mod_cast (show 2 * d j ≤ 2 * n - 2 by have := hd j; omega))

/-- Four sets with a common strict dimension bound cannot cover the ambient vector space.
Source: `Metric.dimH_iUnion` and `Real.dimH_univ_eq_finrank`. -/
theorem bh5_four_sets_noncover (n : ℕ) (S : Fin 4 → Set (Fin n → ℂ))
    (d : ℝ≥0∞) (hd : d < Module.finrank ℝ (Fin n → ℂ))
    (hS : ∀ i, dimH (S i) ≤ d) : ∃ z, ∀ i, z ∉ S i := by
  have hdim : dimH (⋃ i, S i) ≤ d := by
    rw [dimH_iUnion]
    exact iSup_le hS
  have hne : (⋃ i, S i) ≠ univ := by
    intro h
    rw [h, Real.dimH_univ_eq_finrank] at hdim
    exact (not_le_of_gt hd) hdim
  have hex : ∃ z, z ∉ ⋃ i, S i := by
    by_contra! h
    exact hne (Set.eq_univ_of_forall h)
  obtain ⟨z, hz⟩ := hex
  exact ⟨z, fun i hi ↦ hz (mem_iUnion.mpr ⟨i, hi⟩)⟩

end HodgeLean.Adapters

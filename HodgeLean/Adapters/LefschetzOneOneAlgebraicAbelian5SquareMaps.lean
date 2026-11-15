import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5SquareDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open Set Topology
namespace HodgeLean.Adapters

/-- The clamped coordinates belong to the unit interval.
Source: order properties of `min` and `max`. -/
theorem bh5_clamp_bounds (t : ℝ) : 0 ≤ bh5_clamp t ∧ bh5_clamp t ≤ 1 := by
  unfold bh5_clamp
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Outside the parameter disk the clamped map lands on an actual oriented edge.
Source: the affine square parameterization and coordinate clamping. -/
theorem bh5_squareMap_outside
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (q : Fin 1 → ℂ) (hq : q ∉ Metric.closedBall 0 2) :
    ∃ i : Fin 4, ∃ t ∈ Icc (0 : ℝ) 1,
      bh5_squareMap (dim X.left) l m z q = bh4_squareEdge X l m z i t := by
  let s := bh5_clamp (((q 0).re + 1) / 2)
  let t := bh5_clamp (((q 0).im + 1) / 2)
  have hs := bh5_clamp_bounds (((q 0).re + 1) / 2)
  have ht := bh5_clamp_bounds (((q 0).im + 1) / 2)
  change 0 ≤ s ∧ s ≤ 1 at hs
  change 0 ≤ t ∧ t ≤ 1 at ht
  have he : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1 := by
    by_contra! h
    have hr : -1 < (q 0).re ∧ (q 0).re < 1 := by
      constructor
      · by_contra! hh
        apply h.1
        simp [s, bh5_clamp, min_eq_right (by linarith : ((q 0).re + 1) / 2 ≤ 1),
          max_eq_left (by linarith : ((q 0).re + 1) / 2 ≤ 0)]
      · by_contra! hh
        apply h.2.1
        simp [s, bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q 0).re + 1) / 2)]
    have hi : -1 < (q 0).im ∧ (q 0).im < 1 := by
      constructor
      · by_contra! hh
        apply h.2.2.1
        simp [t, bh5_clamp, min_eq_right (by linarith : ((q 0).im + 1) / 2 ≤ 1),
          max_eq_left (by linarith : ((q 0).im + 1) / 2 ≤ 0)]
      · by_contra! hh
        apply h.2.2.2
        simp [t, bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q 0).im + 1) / 2)]
    apply hq
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro i
    fin_cases i
    calc
      ‖q 0‖ ≤ |(q 0).re| + |(q 0).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 := by have := abs_le.mpr ⟨hr.1.le, hr.2.le⟩; have := abs_le.mpr ⟨hi.1.le, hi.2.le⟩; linarith
  rcases he with he | he | he | he
  · refine ⟨3, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    change z + s • (l : Fin (dim X.left) → ℂ) + t • (m : Fin (dim X.left) → ℂ) = _
    simp [bh4_squareEdge, he]
  · refine ⟨1, t, ht, ?_⟩
    change z + s • (l : Fin (dim X.left) → ℂ) + t • (m : Fin (dim X.left) → ℂ) = _
    simp [bh4_squareEdge, he]
  · refine ⟨0, s, hs, ?_⟩
    change z + s • (l : Fin (dim X.left) → ℂ) + t • (m : Fin (dim X.left) → ℂ) = _
    simp [bh4_squareEdge, he]
  · refine ⟨2, 1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
    change z + s • (l : Fin (dim X.left) → ℂ) + t • (m : Fin (dim X.left) → ℂ) = _
    simp [bh4_squareEdge, he]

/-- The equation maps the disk pair to the punctured complex line pair.
Source: functoriality of relative singular cohomology. -/
def bh5_equationPairMap
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Continuous f)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    bh5_diskPair ⟶ puncturedPair ℂ 1 :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun q _ ↦ f (bh5_squareMap (dim X.left) l m z q), by fun_prop⟩)
    (by
      intro q hq hzero
      obtain ⟨i, t, ht, he⟩ := bh5_squareMap_outside X l m z q hq
      exact hnz i t ht (by simpa [he] using congrFun hzero 0))

/-- The period square as a map to the component's relative pair.
Source: functoriality of relative singular cohomology and the exponential cover. -/
def bh5_componentPairMap
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ)
    (ha : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X l m z i t) ∉ cycleComponentSupport X x) :
    bh5_diskPair ⟶ neighborhoodSupportComplementPair
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (cycleComponentSupport X x) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun q ↦ ⟨abelianExp X (bh5_squareMap (dim X.left) l m z q), mem_univ _⟩,
      (continuous_abelianExp X |>.comp (bh5_squareMap (dim X.left) l m z).continuous).subtype_mk _⟩)
    (by
      intro q hq hs
      obtain ⟨i, t, ht, he⟩ := bh5_squareMap_outside X l m z q hq
      exact ha i t ht (by simpa [he] using hs))

end HodgeLean.Adapters

import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8OrientationDefs

/-! # Universal clamped square with values in the coordinate torus

The target pair uses the two coordinate circles as its subspace. The disk exterior
maps to that subspace by clamping. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular Set Topology
open HodgeLean.Foundations.Singular
namespace HodgeLean.Adapters

/-- The coordinate circles forming the one-dimensional boundary of the torus cell.
Source: Hatcher, Algebraic Topology, section 2.2, the square cell structure of the torus. -/
def bh9_torusSkeleton : Set (UnitAddTorus (Fin 2)) := {t | t 0 = 0 ∨ t 1 = 0}

example : (0 : UnitAddTorus (Fin 2)) ∈ bh9_torusSkeleton := Or.inl rfl

/-- The torus relative to its coordinate circles.
Source: Hatcher, Algebraic Topology, section 2.2. -/
def bh9_torusPair : TopPair := TopPair.ofSubset (X := TopCat.of (UnitAddTorus (Fin 2))) bh9_torusSkeleton

example : bh9_torusPair.fst = TopCat.of (UnitAddTorus (Fin 2)) := rfl

/-- The ordered coordinates of the clamped square, reduced modulo one.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.2. -/
def bh9_squareTorus : C((Fin 1 → ℂ), UnitAddTorus (Fin 2)) :=
  ⟨fun q ↦ ![(bh5_clamp (((q 0).re + 1) / 2) : UnitAddCircle),
      (bh5_clamp (((q 0).im + 1) / 2) : UnitAddCircle)], by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> unfold bh5_clamp <;> fun_prop⟩

example : bh9_squareTorus (fun _ ↦ (-1 : ℂ) - Complex.I) = 0 := by
  ext i
  fin_cases i <;> norm_num [bh9_squareTorus, bh5_clamp]

/-- The disk exterior clamps to the boundary of the parameter square.
Source: the norm estimate in the stage-six clamped-square boundary calculation. -/
theorem bh9_clamped_on_boundary (q : bh5_diskPair.snd) :
    bh5_clamp (((q.val 0).re + 1) / 2) = 0 ∨
    bh5_clamp (((q.val 0).re + 1) / 2) = 1 ∨
    bh5_clamp (((q.val 0).im + 1) / 2) = 0 ∨
    bh5_clamp (((q.val 0).im + 1) / 2) = 1 := by
  by_contra! h
  have hr : -1 < (q.val 0).re ∧ (q.val 0).re < 1 := by
    constructor
    · by_contra! hh
      apply h.1
      simp [bh5_clamp, min_eq_right (by linarith : ((q.val 0).re + 1) / 2 ≤ 1),
        max_eq_left (by linarith : ((q.val 0).re + 1) / 2 ≤ 0)]
    · by_contra! hh
      apply h.2.1
      simp [bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q.val 0).re + 1) / 2)]
  have hi : -1 < (q.val 0).im ∧ (q.val 0).im < 1 := by
    constructor
    · by_contra! hh
      apply h.2.2.1
      simp [bh5_clamp, min_eq_right (by linarith : ((q.val 0).im + 1) / 2 ≤ 1),
        max_eq_left (by linarith : ((q.val 0).im + 1) / 2 ≤ 0)]
    · by_contra! hh
      apply h.2.2.2
      simp [bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q.val 0).im + 1) / 2)]
  apply q.property
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro i
  fin_cases i
  calc
    ‖q.val 0‖ ≤ |(q.val 0).re| + |(q.val 0).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 := by
      have := abs_le.mpr ⟨hr.1.le, hr.2.le⟩
      have := abs_le.mpr ⟨hi.1.le, hi.2.le⟩
      linarith


/-- The clamped square as an actual map of relative pairs.
Source: Hatcher, Algebraic Topology, section 2.2, the attaching boundary of the torus cell. -/
def bh9_squareTorusMap : bh5_diskPair ⟶ bh9_torusPair :=
  TopPair.ofSubsetHom (TopCat.ofHom bh9_squareTorus) (by
    intro q hq
    have h := bh9_clamped_on_boundary ⟨q, hq⟩
    change (bh5_clamp (((q 0).re + 1) / 2) : UnitAddCircle) = 0 ∨
      (bh5_clamp (((q 0).im + 1) / 2) : UnitAddCircle) = 0
    rcases h with h | h | h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inl (by rw [h]; exact_mod_cast (AddCircle.coe_period (p := (1 : ℝ))))
    · exact Or.inr (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; exact_mod_cast (AddCircle.coe_period (p := (1 : ℝ)))))

example (q : Fin 1 → ℂ) :
    TopPair.Hom.fst bh9_squareTorusMap q = bh9_squareTorus q := rfl

end HodgeLean.Adapters

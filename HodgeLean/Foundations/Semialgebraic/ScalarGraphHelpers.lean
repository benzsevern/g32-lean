import HodgeLean.Foundations.Program.SchoenTowerT11bGraph
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Actual graph coordinates for maps between Euclidean carriers. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.ScalarTriangulation

/-- A map with its actual Boolean graph identifies its carrier with that graph. -/
def actualGraphHomeomorph {n k : ℕ} (f : s2v_t11b_Formula n)
    (φ : C(f.realize, EuclideanSpace ℝ (Fin k)))
    (G : s2v_t11b_Formula (n + k))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : f.realize,
      (∀ i, z (Fin.castAdd k i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = φ x i)) :
    f.realize ≃ₜ G.realize where
  toFun x := ⟨WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => φ x i)),
    (hG _).mpr ⟨x, fun i => by simp, fun i => by simp⟩⟩
  invFun z := ⟨WithLp.toLp 2 (fun i => z.val (Fin.castAdd k i)), by
    obtain ⟨x, hx, hφ⟩ := (hG z.val).mp z.property
    have heq : WithLp.toLp 2 (fun i : Fin n => z.val (Fin.castAdd k i)) = x.val := by
      ext i; exact hx i
    exact heq.symm ▸ x.property⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    simp only [Fin.append_left]
  right_inv z := by
    obtain ⟨x, hx, hφ⟩ := (hG z.val).mp z.property
    have heq : (⟨WithLp.toLp 2 (fun i : Fin n => z.val (Fin.castAdd k i)),
        by
          have hv : WithLp.toLp 2 (fun i : Fin n => z.val (Fin.castAdd k i)) = x.val := by
            ext i; exact hx i
          exact hv.symm ▸ x.property⟩ : f.realize) = x := by
      apply Subtype.ext
      ext i
      exact hx i
    apply Subtype.ext
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      change φ ⟨WithLp.toLp 2 (fun i => z.val (Fin.castAdd k i)), _⟩ j = z.val (Fin.natAdd n j)
      rw [heq]
      exact (hφ j).symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + k) => ℝ)).comp
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp
          (continuous_subtype_val : Continuous (Subtype.val : f.realize → _))
    · simp only [Fin.append_right]
      exact (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) j).comp φ.continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    exact continuous_pi fun i => (PiLp.continuous_apply 2 _ (Fin.castAdd k i)).comp
      continuous_subtype_val

/-- Coordinatewise equality has a Boolean polynomial formula on any pair of blocks. -/
theorem block_equality_formula {n N : ℕ} (u v : Fin n → Fin N) :
    ∃ H : s2v_t11b_Formula N, ∀ z, z ∈ H.realize ↔ ∀ i, z (u i) = z (v i) := by
  refine ⟨s2v_t11b_zeroFormula
    (∑ i : Fin n, (MvPolynomial.X (u i) - MvPolynomial.X (v i)) ^ 2), ?_⟩
  intro z
  rw [s2v_t11b_realize_zeroFormula]
  simp only [map_sum, map_pow, map_sub, MvPolynomial.eval_X]
  constructor
  · intro h i
    have hi : (z (u i) - z (v i)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (z (u j) - z (v j)))).mp h i
        (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i, sub_self, zero_pow (by omega)]

/-- Fixing the value coordinates of a graph gives an actual level-set formula. -/
theorem actual_level_formula {n k : ℕ} (f : s2v_t11b_Formula n)
    (φ : f.realize → EuclideanSpace ℝ (Fin k))
    (G : s2v_t11b_Formula (n + k))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : f.realize,
      (∀ i, z (Fin.castAdd k i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = φ x i)) (a : EuclideanSpace ℝ (Fin k)) :
    ∃ F : s2v_t11b_Formula n, ∀ z,
      z ∈ F.realize ↔ ∃ x : f.realize, x.val = z ∧ φ x = a := by
  let σ : Fin (n + k) → MvPolynomial (Fin n) ℝ :=
    Fin.addCases MvPolynomial.X (fun i => MvPolynomial.C (a i))
  refine ⟨G.subst σ, ?_⟩
  intro z
  rw [s2v_t11b_realize_subst, hG]
  simp only [σ, Fin.addCases_left, Fin.addCases_right, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  constructor
  · rintro ⟨x, hx, ha⟩
    refine ⟨x, ?_, ?_⟩
    · ext i; exact (hx i).symm
    · ext i; exact (ha i).symm
  · rintro ⟨x, hx, ha⟩
    exact ⟨x, fun i => (congrArg (fun z => z i) hx).symm,
      fun i => (congrArg (fun z => z i) ha).symm⟩

/-- Compact source carriers have compact actual graph carriers. -/
theorem actual_graph_compact {n k : ℕ} (f : s2v_t11b_Formula n)
    (hf : IsCompact f.realize) (φ : C(f.realize, EuclideanSpace ℝ (Fin k)))
    (G : s2v_t11b_Formula (n + k))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : f.realize,
      (∀ i, z (Fin.castAdd k i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = φ x i)) : IsCompact G.realize := by
  letI : CompactSpace f.realize := isCompact_iff_compactSpace.mp hf
  letI : CompactSpace G.realize := (actualGraphHomeomorph f φ G hG).compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- The image of an actual Boolean graph has an exact Boolean carrier formula. -/
theorem actual_image_formula {n k : ℕ} (f : s2v_t11b_Formula n)
    (φ : f.realize → EuclideanSpace ℝ (Fin k))
    (G : s2v_t11b_Formula (n + k))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : f.realize,
      (∀ i, z (Fin.castAdd k i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = φ x i)) :
    ∃ P : s2v_t11b_Formula k, P.realize = Set.range φ := by
  obtain ⟨P, hP⟩ := s2v_hardt_cad5_block_projection_formula G
  refine ⟨P, ?_⟩
  ext y
  rw [hP]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨x, hx, hy⟩ := (hG _).mp hu
    refine ⟨x, ?_⟩
    ext i
    simpa only [Fin.append_right] using (hy i).symm
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, (hG _).mpr ⟨x, fun i => by simp, fun i => by simp⟩⟩

end Semialgebraic.ScalarTriangulation

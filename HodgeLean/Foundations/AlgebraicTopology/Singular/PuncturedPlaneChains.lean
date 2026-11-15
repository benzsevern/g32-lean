import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneBase
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalChains

/-! Integral chain subdivision for exponential loops.
Source: Hatcher, Algebraic Topology (2002), §§2.1–2.2.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Foundations.Program
namespace AlgebraicTopology.Singular.PuncturedPlane

private theorem windingCircle_coe (c : ℂ) (k : ℤ) (s : ℝ) :
    (windingCircle c k (s : UnitAddCircle)).val =
      Complex.exp (c + (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I))) := rfl

/-- Every equal subinterval of the n-turn loop is exactly one positive turn. -/
theorem winding_nat_restr (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    b3Rest2_restr (simplexPath (loopSimplex (windingCircle 0 n)))
      (b3Rest2_frac n j) (b3Rest2_frac n (j + 1)) =
    simplexPath (loopSimplex (windingCircle 0 1)) := by
  apply ContinuousMap.ext
  intro t
  rw [b3Rest2_restr_apply]
  simp only [spec_simplexPath_loopSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  apply Subtype.ext
  rw [windingCircle_coe, windingCircle_coe]
  have har : (b3Rest2_affI (b3Rest2_frac n j) (b3Rest2_frac n (j + 1)) t : ℝ) * n =
      (j : ℝ) + t := by
    change ((b3Rest2_frac n j : ℝ) + (t : ℝ) *
      ((b3Rest2_frac n (j + 1) : ℝ) - (b3Rest2_frac n j : ℝ))) * n = _
    rw [b3Rest2_frac_coe (by omega) hn, b3Rest2_frac_coe (by omega) hn]
    push_cast
    field_simp
    <;> ring
  have hac : ((b3Rest2_affI (b3Rest2_frac n j) (b3Rest2_frac n (j + 1)) t : ℝ) : ℂ) *
      (n : ℂ) = (j : ℂ) + ((t : ℝ) : ℂ) := by exact_mod_cast har
  simp only [zero_add, Int.cast_natCast, Int.cast_one, one_mul]
  rw [← mul_assoc, hac, add_mul, Complex.exp_add]
  have hjexp : Complex.exp ((j : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (j : ℤ)
  rw [hjexp, one_mul]

/-- Subdivision computes the natural winding coefficient in chains modulo
boundaries. -/
theorem winding_nat_chain (n : ℕ) :
    b6m_pathChain (simplexPath (loopSimplex (windingCircle 0 n))) =
      n • b6m_pathChain (simplexPath (loopSimplex (windingCircle 0 1))) := by
  by_cases hn : 0 < n
  · rw [b6m_pathChain_eq_sum _ hn]
    have he := fun j (hj : j ∈ Finset.range n) =>
      congrArg b6m_pathChain (winding_nat_restr n j hn (Finset.mem_range.mp hj))
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const, Finset.card_range]
  · have hn0 : n = 0 := by omega
    subst n
    have he : simplexPath (loopSimplex (windingCircle 0 0)) =
        ContinuousMap.const unitInterval (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) := by
      apply ContinuousMap.ext
      intro t
      apply Subtype.ext
      simp only [spec_simplexPath_loopSimplex, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, windingCircle_coe,
        ContinuousMap.const_apply, Int.cast_zero, zero_mul, mul_zero, add_zero,
        Complex.exp_zero]
    simp only [Nat.cast_zero]
    rw [he, b6m_pathChain_const, zero_smul]

/-- Reversing a canonical winding path negates its integral number of turns. -/
theorem winding_neg_restr (k : ℤ) :
    b3Rest2_restr (simplexPath (loopSimplex (windingCircle 0 k))) 1 0 =
      simplexPath (loopSimplex (windingCircle 0 (-k))) := by
  apply ContinuousMap.ext
  intro t
  rw [b3Rest2_restr_apply]
  simp only [spec_simplexPath_loopSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  apply Subtype.ext
  rw [windingCircle_coe, windingCircle_coe]
  simp only [zero_add, Int.cast_neg]
  have he : ((b3Rest2_affI 1 0 t : ℝ) : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I)) =
      ((t : ℝ) : ℂ) * (-(k : ℂ) * (2 * Real.pi * Complex.I)) +
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
    change (((1 : ℝ) + (t : ℝ) * (0 - 1) : ℝ) : ℂ) * _ = _
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Path subdivision at the two endpoints makes negative winding the additive
inverse in chains modulo boundaries. -/
theorem winding_neg_chain (k : ℤ) :
    b6m_pathChain (simplexPath (loopSimplex (windingCircle 0 (-k)))) =
      -b6m_pathChain (simplexPath (loopSimplex (windingCircle 0 k))) := by
  let g := simplexPath (loopSimplex (windingCircle 0 k))
  have h := b6m_pathChain_subdiv g 0 1 0
  have hc : b3Rest2_restr g 0 0 = ContinuousMap.const unitInterval (g 0) := by
    apply ContinuousMap.ext
    intro t
    simp only [b3Rest2_restr_apply, b3Rest2_affI, Set.Icc.coe_zero,
      sub_self, mul_zero, add_zero]
    rfl
  rw [hc, b6m_pathChain_const, b3Rest2_restr_zero_one,
    winding_neg_restr] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The canonical k-turn exponential loop represents k times the one-turn
loop in integral singular homology of the punctured plane. -/
theorem winding_loop_class (k : ℤ) :
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (windingCircle 0 k)) =
    k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (windingCircle 0 1)) := by
  obtain ⟨j, hj, hJ⟩ := b6m_homology_chain_embedding {z : ℂ // z ≠ 0}
  have hmap (m : ℤ) :
      j (((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (windingCircle 0 m))) =
      b6m_pathChain (simplexPath (loopSimplex (windingCircle 0 m))) := by
    rw [b6m_pathChain, b3Rest2_pathSimplex_simplexPath]
    exact hJ _
  apply hj
  rw [map_zsmul, hmap, hmap]
  cases k with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using winding_nat_chain n
  | negSucc n =>
    have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hn, winding_neg_chain, winding_nat_chain]
    simp only [neg_smul, natCast_zsmul]

end AlgebraicTopology.Singular.PuncturedPlane

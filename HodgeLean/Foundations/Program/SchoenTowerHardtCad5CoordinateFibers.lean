import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CoefficientField
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiberSpecialization
import HodgeLean.Foundations.Program.SchoenTowerHardt2
import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Scalar output projections of actual Boolean graph relations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_coordinate_fiber_formula {n q : ℕ}
    (G : s2v_t11b_Formula (n + q)) (j : Fin q) :
    ∃ F : s2v_t11b_Formula (n + 1),
      ∀ (a : EuclideanSpace ℝ (Fin n)) (t : ℝ),
        WithLp.toLp 2 (Fin.cons t (fun i => a i)) ∈ F.realize ↔
          ∃ y : EuclideanSpace ℝ (Fin q),
            WithLp.toLp 2 (Fin.append (fun i => a i) (fun i => y i)) ∈ G.realize ∧
              y j = t := by
  let u := s2v_hardt2_boundIndex (n + 1) q
  let v := s2v_hardt2_freeIndex (n + 1) q
  let ρ : Fin (n + q) → Fin ((n + 1) + q) := Fin.addCases (fun i => v i.succ) u
  let R : s2v_t11b_Formula ((n + 1) + q) :=
    .inter (s2v_hardt1_rename ρ G)
      (s2v_t11b_zeroFormula (MvPolynomial.X (u j) - MvPolynomial.X (v 0)))
  obtain ⟨F, hF⟩ := s2v_hardt2_repeated_projection R
  refine ⟨F, ?_⟩
  intro a t
  rw [hF]
  let z : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons t (fun i => a i))
  have hcoords (y : Fin q → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert q y z (ρ i)) =
        WithLp.toLp 2 (Fin.append (fun i => a i) y) := by
    ext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simp [ρ, v, s2v_hardt2_insert_free, z]
    · simp [ρ, u, s2v_hardt2_insert_bound]
  have heq (y : Fin q → ℝ) : s2v_hardt2_insert q y z ∈
      (s2v_t11b_zeroFormula (MvPolynomial.X (u j) - MvPolynomial.X (v 0))).realize ↔
        y j = t := by
    rw [s2v_t11b_realize_zeroFormula]
    simp [u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free, z, sub_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    change _ ∧ _ at hy
    rw [s2v_hardt1_realize_rename, hcoords] at hy
    exact ⟨WithLp.toLp 2 y, hy.1, (heq y).mp hy.2⟩
  · rintro ⟨y, hy, hj⟩
    refine ⟨fun i => y i, ?_⟩
    change _ ∧ _
    rw [s2v_hardt1_realize_rename, hcoords]
    exact ⟨hy, (heq _).mpr hj⟩

theorem s2v_hardt_cad5_finite_graph_fiber_algebraic {n q : ℕ}
    (G : s2v_t11b_Formula (n + q)) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ L : Subfield ℝ, K ≤ L → ∀ a : Fin n → L,
        {y : EuclideanSpace ℝ (Fin q) | WithLp.toLp 2
          (Fin.append (fun i => (a i : ℝ)) (fun i => y i)) ∈ G.realize}.Finite →
        ∀ y : EuclideanSpace ℝ (Fin q), WithLp.toLp 2
          (Fin.append (fun i => (a i : ℝ)) (fun i => y i)) ∈ G.realize →
          ∀ j, IsAlgebraic L (y j) := by
  classical
  choose F hF using fun j : Fin q => s2v_hardt_cad5_coordinate_fiber_formula G j
  obtain ⟨K, hK, hcoeff⟩ := s2v_hardt_cad5_formula_coefficient_field
    (fun _ : Fin q => n + 1) F
  refine ⟨K, hK, ?_⟩
  intro L hKL a hf y hy j
  have hlift : ∀ p ∈ (F j).atoms, ∃ r : MvPolynomial (Fin (n + 1)) L,
      MvPolynomial.map L.subtype r = p := by
    intro p hp
    obtain ⟨r, hr⟩ := hcoeff j p hp
    refine ⟨MvPolynomial.map (Subfield.inclusion hKL) r, ?_⟩
    rw [MvPolynomial.map_map]
    exact hr
  have hfin : {t : ℝ | WithLp.toLp 2
      (Fin.cons t (fun i => (a i : ℝ))) ∈ (F j).realize}.Finite := by
    apply (hf.image (fun y => y j)).subset
    intro t ht
    obtain ⟨z, hz, hj⟩ := (hF j (WithLp.toLp 2 (fun i => (a i : ℝ))) t).mp ht
    exact ⟨z, hz, hj⟩
  apply s2v_hardt_cad5_finite_specialized_fiber_algebraic L (F j) hlift a hfin (y j)
  exact (hF j (WithLp.toLp 2 (fun i => (a i : ℝ))) (y j)).mpr ⟨y, hy, rfl⟩

end HodgeLean.Foundations.Program

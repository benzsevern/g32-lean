import HodgeLean.Foundations.Program.SchoenTowerHardtCad5RootTupleLimits
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericSpecialization
import HodgeLean.Foundations.Program.SchoenTowerHardtCad2
import HodgeLean.Foundations.Program.SchoenTowerT11bCylindricalEncoding

/-! Generic ambient limit membership from coordinatewise polynomial constraints. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_generic_polynomial_fiber_limit {n q : ℕ}
    (S : s2v_t11b_Formula (q + n)) (poly : Fin q → MvPolynomial (Fin (n + 1)) ℝ)
    (hp : ∀ i, poly i ≠ 0)
    (hzero : ∀ (t : EuclideanSpace ℝ (Fin q)) (a : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ S.realize →
        ∀ i, MvPolynomial.eval (Fin.cons (t i) (fun v => a v)) (poly i) = 0) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ L : Subfield ℝ, K ≤ L → ∀ a : EuclideanSpace ℝ (Fin n),
        AlgebraicIndependent L (fun i => a i) → ∀ t : EuclideanSpace ℝ (Fin q),
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ closure S.realize →
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ S.realize := by
  classical
  let P := fun i => MvPolynomial.finSuccEquiv ℝ n (poly i)
  obtain ⟨Kp, hKp, hPcoeff⟩ := s2v_hardt_cad5_formula_coefficient_field
    (fun _ : Fin q => n + 1) (fun i => s2v_t11b_Formula.nonneg (poly i))
  obtain ⟨m, C, hC, _, hcover, _, hstatus, hroots⟩ :=
    s2v_hardt_cad2_root_partition P (fun i : Fin 0 => Fin.elim0 i)
  choose r ψ hψ hm hroot using hroots
  choose g hg using fun j => s2v_hardt_cad2_section_formulas P (C j) (hC j)
    (ψ j) (hψ j) (hm j) (hroot j) (C j) (fun _ h => h)
  have hlocal (j : Fin m) :
      ∃ Kj : Subfield ℝ, Countable Kj ∧
      ∀ L : Subfield ℝ, Kj ≤ L → ∀ a : EuclideanSpace ℝ (Fin n),
        a ∈ (C j).realize → AlgebraicIndependent L (fun i => a i) →
        (∀ i, (P i).map (MvPolynomial.eval (fun v => a v)) ≠ 0) →
        ∀ t : EuclideanSpace ℝ (Fin q),
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ closure S.realize →
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ S.realize := by
    by_cases hN : ∀ i, ∀ a : (C j).realize, (P i).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0
    · have hTuple : ∀ (t : EuclideanSpace ℝ (Fin q)) (a : (C j).realize),
          WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a.val i)) ∈ S.realize →
            ∀ i, ∃ l, t i = ψ j l a := by
        intro t a ht i
        apply (hroot j a (t i)).mp
        refine ⟨i, hN i a, ?_⟩
        rw [s2v_t11b_finSucc_family_eval]
        exact hzero t a.val ht i
      obtain ⟨Kj, hKj, hlim⟩ := s2v_hardt_cad5_root_tuple_limit_mem
        (C j) (ψ j) (hψ j) (g j) (hg j) S hTuple
      exact ⟨Kj, hKj, fun L hKL a ha hgen _ => hlim L hKL a ha hgen⟩
    · refine ⟨Kp, hKp, ?_⟩
      intro L _ a ha _ hn t _
      obtain ⟨i, hi⟩ := not_forall.mp hN
      rcases hstatus j i with hz | hnz
      · exact ((hn i) (hz ⟨a, ha⟩)).elim
      · exact (hi hnz).elim
  choose Kj hKj hlim using hlocal
  let s : Set ℝ := (Kp : Set ℝ) ∪ ⋃ j, (Kj j : Set ℝ)
  have hs : s.Countable := Set.Countable.union (by
    letI := hKp
    exact Set.to_countable _) (Set.countable_iUnion (fun j => by
      letI := hKj j
      exact Set.to_countable _))
  let K : Subfield ℝ := Subfield.closure s
  have hK : Countable K := s2v_hardt_cad5_countable_coefficient_field s hs
  have hKpK : Kp ≤ K := fun _ hc => Subfield.subset_closure (Or.inl hc)
  have hKjK (j : Fin m) : Kj j ≤ K := fun _ hc =>
    Subfield.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨j, hc⟩))
  refine ⟨K, hK, ?_⟩
  intro L hKL a hgen t ht
  have hnonzero (i : Fin q) : (P i).map (MvPolynomial.eval (fun v => a v)) ≠ 0 := by
    obtain ⟨b, hb⟩ := hPcoeff i (poly i) (Finset.mem_singleton_self (poly i))
    let bL := MvPolynomial.map (Subfield.inclusion (hKpK.trans hKL)) b
    have hbL : MvPolynomial.map L.subtype bL = poly i := by
      rw [MvPolynomial.map_map]
      exact hb
    have hbn : bL ≠ 0 := by
      intro hz
      apply hp i
      rw [← hbL, hz, map_zero]
    have hn := s2v_hardt_cad5_generic_specialization_ne_zero L bL hbn (fun v => a v) hgen
    simpa only [hbL] using hn
  have ha : a ∈ ⋃ j, (C j).realize := by rw [hcover]; exact Set.mem_univ a
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
  exact hlim j L ((hKjK j).trans hKL) a hj hgen hnonzero t ht

end HodgeLean.Foundations.Program

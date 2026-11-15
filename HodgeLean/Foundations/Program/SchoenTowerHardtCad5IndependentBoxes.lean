import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericPoints
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! Algebraically independent points in real coordinate boxes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_countable_adjoin_coordinates {d : ℕ}
    (K : Subfield ℝ) [Countable K] (x : Fin d → ℝ) :
    Countable (Algebra.adjoin K (Set.range x)) := by
  letI : Countable (Fin d →₀ ℕ) := (Finsupp.graph_injective (Fin d) ℕ).countable
  letI : Countable ((Fin d →₀ ℕ) →₀ K) :=
    (Finsupp.graph_injective (Fin d →₀ ℕ) K).countable
  letI : Countable (MvPolynomial (Fin d) K) :=
    AddMonoidAlgebra.coeff_injective.countable
  let f : MvPolynomial (Fin d) K → Algebra.adjoin K (Set.range x) :=
    fun p => ⟨MvPolynomial.aeval x p, by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : ℝ) ∈ (MvPolynomial.aeval (R := K) x).range := by
      simpa only [← Algebra.adjoin_range_eq_range_aeval] using a.property
    obtain ⟨p, hp⟩ := ha
    exact ⟨p, Subtype.ext hp⟩
  exact hf.countable

theorem s2v_hardt_cad5_independent_box_point (K : Subfield ℝ) [Countable K] (d : ℕ) :
    ∃ x : EuclideanSpace ℝ (Fin d), AlgebraicIndependent K (fun i => x i) ∧
      ∀ i, -1 < x i ∧ x i < 1 := by
  induction d with
  | zero =>
    exact ⟨0, algebraicIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ d ih =>
    obtain ⟨x, hx, hbox⟩ := ih
    let A := Algebra.adjoin K (Set.range (fun i => x i))
    letI : Countable A := s2v_hardt_cad5_countable_adjoin_coordinates K (fun i => x i)
    have hd : Dense {t : ℝ | Transcendental A t} :=
      (s2v_hardt_cad5_countable_algebraic A).dense_compl ℝ
    obtain ⟨t, ht, hbt⟩ := hd.exists_mem_open isOpen_Ioo
      (show (Set.Ioo (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    let y : Fin (d + 1) → ℝ := fun i => (finSuccEquiv d i).elim t (fun i => x i)
    have hy : AlgebraicIndependent K y :=
      ((hx.option_iff_transcendental t).mpr ht).comp (finSuccEquiv d)
        (finSuccEquiv d).injective
    refine ⟨WithLp.toLp 2 y, hy, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [y] using hbt
    · simpa [y] using hbox j

theorem s2v_hardt_cad5_independent_rectangle_point (K : Subfield ℝ) [Countable K]
    (d : ℕ) (l u : Fin d → ℝ) (hlu : ∀ i, l i < u i) :
    ∃ x : EuclideanSpace ℝ (Fin d), AlgebraicIndependent K (fun i => x i) ∧
      ∀ i, l i < x i ∧ x i < u i := by
  induction d with
  | zero =>
    exact ⟨0, algebraicIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ d ih =>
    obtain ⟨x, hx, hrect⟩ := ih (fun i => l i.succ) (fun i => u i.succ)
      (fun i => hlu i.succ)
    let A := Algebra.adjoin K (Set.range (fun i => x i))
    letI : Countable A := s2v_hardt_cad5_countable_adjoin_coordinates K (fun i => x i)
    have hd : Dense {t : ℝ | Transcendental A t} :=
      (s2v_hardt_cad5_countable_algebraic A).dense_compl ℝ
    obtain ⟨t, ht, hbt⟩ := hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr (hlu 0))
    let y : Fin (d + 1) → ℝ := fun i => (finSuccEquiv d i).elim t (fun i => x i)
    have hy : AlgebraicIndependent K y :=
      ((hx.option_iff_transcendental t).mpr ht).comp (finSuccEquiv d)
        (finSuccEquiv d).injective
    refine ⟨WithLp.toLp 2 y, hy, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [y] using hbt
    · simpa [y] using hrect j

theorem s2v_hardt_cad5_independent_open_point (K : Subfield ℝ) [Countable K] {d : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, AlgebraicIndependent K (fun i => x i) := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hW : IsOpen ((WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' U) :=
    hU.preimage (PiLp.continuous_toLp 2 _)
  obtain ⟨V, hV, hsub⟩ := isOpen_pi_iff'.mp hW (fun i => a i) ha
  choose l u hlu hI using fun i => (hV i).1.exists_Ioo_subset ⟨a i, (hV i).2⟩
  obtain ⟨x, hx, hrect⟩ := s2v_hardt_cad5_independent_rectangle_point K d l u hlu
  refine ⟨x, ?_, hx⟩
  exact hsub (fun i _ => hI i (hrect i))

end HodgeLean.Foundations.Program

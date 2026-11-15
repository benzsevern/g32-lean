import HodgeLean.Foundations.Program.SchoenTowerHardtCad5AlgebraicFibers
import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Coefficient-field control under actual polynomial fiber substitutions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_subst_atom_lift {n m : ℕ} (K : Subfield ℝ)
    (f : s2v_t11b_Formula n)
    (hlift : ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin n) K,
      MvPolynomial.map K.subtype q = p)
    (σ : Fin n → MvPolynomial (Fin m) K) :
    ∀ p ∈ (f.subst (fun i => MvPolynomial.map K.subtype (σ i))).atoms,
      ∃ q : MvPolynomial (Fin m) K, MvPolynomial.map K.subtype q = p := by
  classical
  induction f with
  | nonneg p =>
    intro q hq
    change q ∈ {MvPolynomial.bind₁ _ p} at hq
    obtain rfl := Finset.mem_singleton.mp hq
    obtain ⟨a, ha⟩ := hlift p (Finset.mem_singleton_self p)
    refine ⟨MvPolynomial.bind₁ σ a, ?_⟩
    rw [MvPolynomial.map_bind₁, ha]
  | compl f ih => exact ih hlift
  | inter f g ihf ihg =>
    intro p hp
    change p ∈ _ ∪ _ at hp
    rcases Finset.mem_union.mp hp with hf | hg
    · exact ihf (fun p hp => hlift p (Finset.mem_union_left _ hp)) p hf
    · exact ihg (fun p hp => hlift p (Finset.mem_union_right _ hp)) p hg

theorem s2v_hardt_cad5_finite_specialized_fiber_algebraic {n : ℕ} (K : Subfield ℝ)
    (f : s2v_t11b_Formula (n + 1))
    (hlift : ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin (n + 1)) K,
      MvPolynomial.map K.subtype q = p)
    (a : Fin n → K)
    (hf : {t : ℝ | WithLp.toLp 2
      (Fin.cons t (fun i => (a i : ℝ))) ∈ f.realize}.Finite)
    (t : ℝ) (ht : WithLp.toLp 2 (Fin.cons t (fun i => (a i : ℝ))) ∈ f.realize) :
    IsAlgebraic K t := by
  let σ : Fin (n + 1) → MvPolynomial (Fin 1) K :=
    Fin.cases (MvPolynomial.X 0) (fun i => MvPolynomial.C (a i))
  let g := f.subst (fun i => MvPolynomial.map K.subtype (σ i))
  have hg (z : EuclideanSpace ℝ (Fin 1)) : z ∈ g.realize ↔
      WithLp.toLp 2 (Fin.cons (z 0) (fun i => (a i : ℝ))) ∈ f.realize := by
    rw [s2v_t11b_realize_subst]
    have heq : WithLp.toLp 2 (fun i =>
        MvPolynomial.eval (fun j => z j) (MvPolynomial.map K.subtype (σ i))) =
        WithLp.toLp 2 (Fin.cons (z 0) (fun i => (a i : ℝ))) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [σ]
      · simp [σ]
    rw [heq]
  have hfin : g.realize.Finite := by
    apply (hf.image (fun t => WithLp.toLp 2 (fun _ : Fin 1 => t))).subset
    intro z hz
    refine ⟨z 0, (hg z).mp hz, ?_⟩
    ext i
    exact congrArg (fun j : Fin 1 => z j) (Subsingleton.elim 0 i)
  exact s2v_hardt_cad5_finite_line_algebraic K g
    (s2v_hardt_cad5_subst_atom_lift K f hlift σ) hfin
    (WithLp.toLp 2 (fun _ : Fin 1 => t)) ((hg _).mpr ht)

end HodgeLean.Foundations.Program

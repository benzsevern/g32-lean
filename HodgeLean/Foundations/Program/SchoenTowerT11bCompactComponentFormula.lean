import HodgeLean.Foundations.Program.SchoenTowerT11bBallFormula

/-! Boolean formulas selecting actual compact components.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A compact relatively open subset of an actual Boolean realization is itself a Boolean realization.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compact relative component selection step. -/
theorem s2v_t11b_compact_open_subtype_formula {n : ℕ} (f : s2v_t11b_Formula n)
    (A : Set f.realize) (hA : IsCompact A) (ho : IsOpen A) :
    ∃ g : s2v_t11b_Formula n, g.realize = Subtype.val '' A := by
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp ho
  have hAO : Subtype.val '' A ⊆ O := by
    rintro x ⟨y, hy, rfl⟩
    rw [← hpre] at hy
    exact hy
  obtain ⟨g, hAg, hgO⟩ := s2v_t11b_compact_boolean_neighborhood
    (Subtype.val '' A) O (hA.image continuous_subtype_val) hO hAO
  refine ⟨.inter f g, ?_⟩
  ext x
  change (x ∈ f.realize ∧ x ∈ g.realize) ↔ x ∈ Subtype.val '' A
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨⟨x, hf⟩, ?_, rfl⟩
    rw [← hpre]
    exact hgO hg
  · intro hx
    have hg := hAg hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y.property, hg⟩

/-- Every compact actual component of a Boolean realization has a Boolean polynomial description in the original ambient coordinates.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compact actual component description step. -/
theorem s2v_t11b_compact_component_formula {n : ℕ} (f : s2v_t11b_Formula n)
    (x : f.realize) (hc : IsCompact (connectedComponent x)) :
    ∃ g : s2v_t11b_Formula n, g.realize = Subtype.val '' connectedComponent x := by
  letI := s2v_t11b_formula_finite_components f
  exact s2v_t11b_compact_open_subtype_formula f (connectedComponent x) hc
    (s2v_t11b_component_clopen_of_finite x).isOpen

/-- A compact Boolean realization has a finite disjoint partition by connected Boolean realizations in the original ambient space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compact Boolean component partition step. -/
theorem s2v_t11b_compact_boolean_component_partition {n : ℕ}
    (f : s2v_t11b_Formula n) (hf : IsCompact f.realize) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize ∧ (c i).realize ⊆ f.realize) ∧
      (∀ y, y ∈ f.realize → ∃ i, y ∈ (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      ∀ i, ∃ x : f.realize, (c i).realize = Subtype.val '' connectedComponent x := by
  classical
  letI : CompactSpace f.realize := isCompact_iff_compactSpace.mp hf
  obtain ⟨m, U, hU, hcover, hdisj, hcomp⟩ := s2v_t11b_formula_finite_component_partition f
  choose x hx using hcomp
  choose c hc using fun i => s2v_t11b_compact_component_formula f (x i)
    isClosed_connectedComponent.isCompact
  have he : ∀ i, (c i).realize = U i := fun i => (hc i).trans (hx i).symm
  refine ⟨m, c, ?_, ?_, ?_, fun i => ⟨x i, hc i⟩⟩
  · intro i
    rw [he]
    exact hU i
  · intro y hy
    obtain ⟨i, hi⟩ := hcover y hy
    exact ⟨i, (he i).symm ▸ hi⟩
  · intro i j hij
    rw [he, he]
    exact hdisj hij

end HodgeLean.Foundations.Program

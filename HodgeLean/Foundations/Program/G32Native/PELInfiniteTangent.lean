import HodgeLean.Foundations.Program.G32Native.PELFullLieContainment

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MvPolynomial TopologicalSpace
variable {k : Type*} [Field k] {n : ℕ}

/-- The one-element matrix group in any dimension. -/
def pelTrivialMatrixGroup (k : Type*) [Field k] (n : ℕ) : MatrixAlgGroup k n :=
  g1_ofEquations {f | ∃ i j : Fin n, f = X (i, j) - C ((1 : Matrix (Fin n) (Fin n) k) i j)}
    ⊥ (by
      intro g
      change g = 1 ↔ ∀ f, (∃ i j : Fin n, f = X (i, j) - C ((1 : Matrix (Fin n) (Fin n) k) i j)) →
        eval (g1_coords g) f = 0
      constructor
      · rintro rfl f ⟨i, j, rfl⟩
        simp [g1_coords]
      · intro h
        apply Units.ext
        ext i j
        change (g : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) i j
        have hf := h _ ⟨i, j, rfl⟩
        simpa only [map_sub, eval_X, eval_C, sub_eq_zero, g1_coords] using hf)

/-- A matrix algebraic group with a one-element identity component is finite. -/
lemma pel_finite_of_trivial_identityComponent (G : MatrixAlgGroup k n)
    (hG : g1_identityComponent G ⊆ {1}) :
    (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)).Finite := by
  letI := g1_zariski k n
  letI := g1_noetherianSpace (k := k) (n := n)
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (g1_isClosed_carrier G)
  rw [hSU]
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨a, ha⟩ := (hSi t ht).nonempty
  have htG : t ⊆ G.carrier := by
    rw [hSU]
    exact Set.subset_sUnion_of_mem ht
  refine (Set.finite_singleton a).subset ?_
  intro g hg
  have hpre : IsPreconnected ((fun u => a⁻¹ * u) '' t) :=
    (hSi t ht).2.isPreconnected.image _ (g1_continuous_mul_left a⁻¹).continuousOn
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin n) k) ∈ (fun u => a⁻¹ * u) '' t :=
    ⟨a, ha, inv_mul_cancel a⟩
  have hsub : (fun u => a⁻¹ * u) '' t ⊆ G.carrier := by
    rintro _ ⟨u, hu, rfl⟩
    exact G.carrier.mul_mem (G.carrier.inv_mem (htG ha)) (htG hu)
  have h := hG (hpre.subset_connectedComponentIn h1 hsub ⟨g, hg, rfl⟩)
  have heq : a⁻¹ * g = 1 := h
  simpa only [Set.mem_singleton_iff] using (inv_mul_eq_one.mp heq).symm

/-- Infinite matrix algebraic groups have nonzero tangent space in
characteristic zero.
Source: Borel, Linear Algebraic Groups, second edition, §§1.2, 3.6, 7.1. -/
theorem pel_lie_ne_bot_of_infinite [IsAlgClosed k] [CharZero k] (G : MatrixAlgGroup k n)
    (hG : (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)).Infinite) :
    g1_lieAlgebra G ≠ ⊥ := by
  intro hLie
  have h := pel_identityComponent_subset_of_lie_le G (pelTrivialMatrixGroup k n)
    (by rw [hLie]; exact bot_le)
  exact hG (pel_finite_of_trivial_identityComponent G h)

#print axioms pel_lie_ne_bot_of_infinite
end HodgeLean.Foundations.Program.GeneralTypeIII

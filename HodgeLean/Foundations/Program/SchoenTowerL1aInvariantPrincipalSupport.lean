import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantPrincipal
import HodgeLean.Foundations.Program.SchoenTowerPointJets
import Mathlib.Algebra.Algebra.Operations

/-! # Invariant principal neighborhoods of actual finite support

Implication from an ideal avoiding a finite rational orbit to a descended
invariant section in that ideal which remains nonzero at the specified point.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An ideal avoiding every point of a finite rational orbit contains a
descended invariant section nonzero at that point.
Source: Stacks Project, tag 04A9; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2v_l1a_invariant_principal_support
    {A B K G : Type*} [CommRing A] [CommRing B] [Field K] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (q : B →+* A)
    (himage : ∀ a : A, a ∈ Set.range q ↔ ∀ g : G, g • a = a)
    (φ : A →ₐ[K] K) (I : Ideal A)
    (hI : ∀ g : G, ∃ r ∈ I, φ (g • r) ≠ 0) :
    ∃ c : B, q c ∈ I ∧ φ (q c) ≠ 0 := by
  classical
  let ψ (g : G) : A →ₐ[K] K := φ.comp (MulSemiringAction.toAlgHom K A g)
  let κ := Set.range ψ
  letI : Fintype κ := (Set.finite_range ψ).fintype
  have hex (k : κ) : ∃ r ∈ I, k.1 r ≠ 0 := by
    obtain ⟨g, hg⟩ := k.2
    obtain ⟨r, hr, hnr⟩ := hI g
    refine ⟨r, hr, ?_⟩
    rw [← hg]
    exact hnr
  choose r hr hnr using hex
  obtain ⟨d, hd, hdv⟩ := s2t_unit_value_in_span (fun k : κ => k.1)
    Subtype.val_injective r hnr
  have hdI : d ∈ I := (Ideal.span_le.mpr (by
    rintro _ ⟨k, rfl⟩
    exact hr k)) hd
  have hnd (g : G) : φ (g • d) ≠ 0 := by
    have H := hdv ⟨ψ g, ⟨g, rfl⟩⟩
    change φ (g • d) = 1 at H
    rw [H]
    exact one_ne_zero
  obtain ⟨c, hc, hnc, _⟩ := s2v_l1a_invariant_principal_refinement q himage
    φ.toRingHom I d hdI hnd
  exact ⟨c, hc, hnc⟩

end HodgeLean.Foundations.Program

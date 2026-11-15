import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteNakayama
import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedMinimalGenerator
import HodgeLean.Foundations.Program.G32Native.PairedC3RegularQuotientRank
import HodgeLean.Foundations.Program.G32Native.RegularQuotientParameters

/-! # Pointwise adapted slice generators and ambient parameters -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native

/-- At a regular point of a regular slice with a regular hyperplane section,
the adapted branch difference extends to slice generators and labelled
ambient parameters. All equations are constructed in this one local ring.
Source: Stacks Project, Tags 00NR and 00NQ; Atiyah–Macdonald, Introduction
to Commutative Algebra, Proposition 2.8; Hartshorne, Algebraic Geometry, II.8. -/
theorem paired_c3_adapted_local_parameters
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)]
    (hI : I ≤ maximalIdeal R) (k : ℕ)
    (hcodim : ringKrullDim (R ⧸ I) + (k + 1) = ringKrullDim R)
    (u v : maximalIdeal R)
    (htrans : LinearIndependent (R ⧸ maximalIdeal R)
      ![(maximalIdeal R).toCotangent u, (maximalIdeal R).toCotangent v])
    (a : R) (ht : (v : R) - a * (u : R) ∈ I)
    [IsRegularLocalRing (R ⧸ (I ⊔ Ideal.span {(u : R)}))]
    (hsection : ringKrullDim (R ⧸ (I ⊔ Ideal.span {(u : R)})) + (k + 2) =
      ringKrullDim R) :
    ∃ (t : Fin (k + 1) → R),
      t 0 = (v : R) - a * (u : R) ∧ Ideal.span (Set.range t) = I ∧
      ∃ (n : ℕ) (z : Fin n → R) (e : Fin (k + 2) ↪ Fin n),
        IsRegularSystemOfParameters z ∧ z (e 0) = (u : R) ∧
        (∀ j, z (e j.succ) = t j) ∧
        ∃ (w : Fin n → maximalIdeal R)
          (b : Module.Basis (Fin n) (ResidueField R) (maximalIdeal R).Cotangent),
          (∀ j, (w j : R) = z j) ∧ ∀ j, b j = (maximalIdeal R).toCotangent (w j) := by
  letI : Module.Finite R I := Module.Finite.iff_fg.mpr I.fg_of_isNoetherianRing
  have hmin := paired_c3_adapted_minimal I hI u v htrans a ht
  have hdim := paired_c3_regular_quotient_generator_rank I hI (k + 1) hcodim
  obtain ⟨c, b, hc0, hc, hspan⟩ := paired_c3_finite_generators_first
    (⟨(v : R) - a * (u : R), ht⟩ : I) hmin k hdim
  let t : Fin (k + 1) → R := fun j => (c j : R)
  have hgen : Ideal.span (Set.range t) = I := by
    have hm := congrArg (Submodule.map I.subtype) hspan
    simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      ← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using hm
  let f : Fin (k + 2) → R := Fin.cons (u : R) t
  have hf : ∀ j, f j ∈ maximalIdeal R := by
    intro j
    refine Fin.cases u.property (fun i => hI (c i).property) j
  have hfg : Ideal.span (Set.range f) = I ⊔ Ideal.span {(u : R)} := by
    rw [Fin.range_cons, Ideal.span_insert, hgen, sup_comm]
  obtain ⟨n, z, e, hz, he⟩ := g32l4_regular_quotient_labelled_parameters
    (I ⊔ Ideal.span {(u : R)}) f hf hfg (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using hsection)
  have hzmem (j : Fin n) : z j ∈ maximalIdeal R := by
    rw [← hz.1]
    exact Ideal.subset_span (Set.mem_range_self j)
  obtain ⟨B, hB⟩ := exists_basis_cotangentSpace_of_span_eq z hz.1.symm hz.2
  refine ⟨t, congrArg Subtype.val hc0, hgen, n, z, e, hz, he 0, ?_, (fun j => ⟨z j, hzmem j⟩), B, (fun _ => rfl), ?_⟩
  · intro j
    exact he j.succ
  · intro j
    exact hB j

#print axioms paired_c3_adapted_local_parameters
end HodgeLean.Foundations.Program.G32Native

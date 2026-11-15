import HodgeLean.Adapters.DegreeOneSplitProofs

/-! # Degree-one lattice split specification (FROZEN)

This file specifies the linear-algebra split on the complex tangent space used by the S12
uniformization. No statement assumes `HodgeDecomposition`, `BettiDeRhamIso`, or a finiteness
hypothesis. The comparison with upstream cohomology is not claimed because the required
degree-one singular-cohomology/period-character map is not yet in the API. Thus this is the
lattice-side target, not an implication from an already-assumed Hodge decomposition.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- The complex-valued real dual of the S12 tangent space is spanned by its complex-linear and
conjugate-linear summands.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
theorem spec_H1_lattice_split (g : ℕ) :
    degreeOneLatticeHolomorphic g ⊔ degreeOneLatticeAntiholomorphic g = ⊤ :=
  spec_H1_lattice_split_aux g

example (g : ℕ) : degreeOneLatticeHolomorphic g ⊔ degreeOneLatticeAntiholomorphic g = ⊤ :=
  spec_H1_lattice_split g

/-- The complex-linear and conjugate-linear summands have zero intersection.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
theorem spec_H1_lattice_disjoint (g : ℕ) :
    Disjoint (degreeOneLatticeHolomorphic g) (degreeOneLatticeAntiholomorphic g) :=
  spec_H1_lattice_disjoint_aux g

example (g : ℕ) : Disjoint (degreeOneLatticeHolomorphic g)
    (degreeOneLatticeAntiholomorphic g) := spec_H1_lattice_disjoint g

/-- The complex-linear summand in the dual of `ℂ^g` has complex dimension `g`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and Theorem 1.4.1. -/
theorem spec_H1_lattice_holomorphic_dimension (g : ℕ) :
    Module.finrank ℂ (degreeOneLatticeHolomorphic g) = g :=
  spec_H1_lattice_holomorphic_dimension_aux g

example (g : ℕ) : Module.finrank ℂ (degreeOneLatticeHolomorphic g) = g :=
  spec_H1_lattice_holomorphic_dimension g

/-- The conjugate-linear summand in the dual of `ℂ^g` has complex dimension `g`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and Theorem 1.4.1. -/
theorem spec_H1_lattice_antiholomorphic_dimension (g : ℕ) :
    Module.finrank ℂ (degreeOneLatticeAntiholomorphic g) = g :=
  spec_H1_lattice_antiholomorphic_dimension_aux g

example (g : ℕ) : Module.finrank ℂ (degreeOneLatticeAntiholomorphic g) = g :=
  spec_H1_lattice_antiholomorphic_dimension g

/-- Conjugating the value exchanges the two lattice-side summands.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
theorem spec_H1_lattice_conjugation_exchanges (g : ℕ) :
    (∀ f ∈ degreeOneLatticeHolomorphic g,
      degreeOneLatticeConjugate g f ∈ degreeOneLatticeAntiholomorphic g) ∧
    (∀ f ∈ degreeOneLatticeAntiholomorphic g,
      degreeOneLatticeConjugate g f ∈ degreeOneLatticeHolomorphic g) :=
  spec_H1_lattice_conjugation_exchanges_aux g

example (g : ℕ) (f : DegreeOneLatticeDual g) (hf : f ∈ degreeOneLatticeHolomorphic g) :
    degreeOneLatticeConjugate g f ∈ degreeOneLatticeAntiholomorphic g :=
  (spec_H1_lattice_conjugation_exchanges g).1 f hf

end HodgeLean.Adapters

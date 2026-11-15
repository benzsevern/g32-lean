import HodgeLean.Foundations.Program.SchoenFixedRingGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite generation over coefficients concentrated in degree zero implies
finite generation over the actual degree-zero ring. -/
theorem s2_graded_finiteType_over_zero {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hR : ∀ r : R, algebraMap R A r ∈ 𝒜 0) : Algebra.FiniteType (𝒜 0) A := by
  let f : R →+* 𝒜 0 :=
    { toFun := fun r => ⟨algebraMap R A r, hR r⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  letI : Algebra R (𝒜 0) := f.toAlgebra
  letI : IsScalarTower R (𝒜 0) A := IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) A

/-- The actual degree-zero ring of a grading-preserving finite-group invariant
ring is a coefficient ring over which those invariants are finitely generated. -/
theorem s2_fixedRing_finiteType_over_zero {R A : Type} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hR : ∀ r : R, algebraMap R A r ∈ 𝒜 0) :
    Algebra.FiniteType (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G) 0)
      (FixedPoints.subring A G) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI : Algebra R (FixedPoints.subring A G) :=
    inferInstanceAs (Algebra R (FixedPoints.subalgebra R A G))
  haveI : Algebra.FiniteType R (FixedPoints.subring A G) := s2_fixedAlgebra_finiteType R A G
  apply s2_graded_finiteType_over_zero (R := R) (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))
  intro r
  exact hR r

/-- Grading-preserving finite-group invariants have finitely many homogeneous
positive-degree generators over their actual degree-zero ring. -/
theorem s2_fixedRing_homogeneous_generators {R A : Type} [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hR : ∀ r : R, algebraMap R A r ∈ 𝒜 0) :
    ∃ s : Finset (FixedPoints.subring A G),
      Algebra.adjoin (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G) 0)
        (s : Set (FixedPoints.subring A G)) = ⊤ ∧
      ∀ a ∈ s, ∃ n : ℕ, 0 < n ∧ a.val ∈ 𝒜 n := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  haveI := s2_fixedRing_finiteType_over_zero 𝒜 G hgrade hR
  obtain ⟨s, hs, hhom⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero
    (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G))
  refine ⟨s, hs, ?_⟩
  intro a ha
  obtain ⟨n, hn, hmem⟩ := hhom a ha
  exact ⟨n, Nat.pos_of_ne_zero hn, hmem⟩

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleProjCoordinateImmersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Retain the chosen homogeneous coordinates and set the others to zero.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_gradedCoordinateProjection {ι κ : Type} (e : κ ↪ ι) :
    homogeneousSubmodule ι (ULift.{0} ℤ) →+*ᵍ homogeneousSubmodule κ (ULift.{0} ℤ) where
  __ := (MvPolynomial.killCompl (R := ULift.{0} ℤ) e.injective).toRingHom
  map_mem := by
    classical
    intro d p hp
    change (MvPolynomial.killCompl (R := ULift.{0} ℤ) e.injective p).IsHomogeneous d
    dsimp only [MvPolynomial.killCompl]
    have hh (j : ι) :
        (if h : j ∈ Set.range e then
          (X ((Equiv.ofInjective e e.injective).symm ⟨j, h⟩) : MvPolynomial κ (ULift.{0} ℤ))
        else 0).IsHomogeneous 1 := by
      split_ifs
      · exact isHomogeneous_X _ _
      · exact isHomogeneous_zero κ (ULift.{0} ℤ) 1
    simpa only [one_mul] using hp.aeval _ hh

/-- Include the retained coordinates as a graded section of coordinate elimination.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_gradedCoordinateSection {ι κ : Type} (e : κ ↪ ι) :
    homogeneousSubmodule κ (ULift.{0} ℤ) →+*ᵍ homogeneousSubmodule ι (ULift.{0} ℤ) where
  __ := (MvPolynomial.rename e).toRingHom
  map_mem := fun h => h.rename_isHomogeneous

/-- Projection followed by the retained-coordinate section recovers every retained polynomial.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_gradedCoordinate_retraction {ι κ : Type} (e : κ ↪ ι)
    (p : MvPolynomial κ (ULift.{0} ℤ)) :
    s2e_gradedCoordinateProjection e (s2e_gradedCoordinateSection e p) = p := by
  exact MvPolynomial.killCompl_rename_app e.injective p

/-- Coordinate elimination has the generated coordinate ideal as its kernel over the coefficient ring.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; polynomial coordinate elimination. -/
theorem s2e_polynomial_coordinate_kernel
    (R : Type) [CommRing R] (n : ℕ) (T : Finset (Fin n)) :
    RingHom.ker (MvPolynomial.killCompl
      (R := R) (f := fun i : {i : Fin n // i ∉ T} => i.val)
      Subtype.val_injective).toRingHom =
      Ideal.span ((MvPolynomial.X (R := R)) '' (↑T : Set (Fin n))) := by
  classical
  let f : {i : Fin n // i ∉ T} → Fin n := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  ext p
  rw [RingHom.mem_ker, MvPolynomial.mem_ideal_span_X_image]
  change killCompl hf p = 0 ↔ _
  constructor
  · intro hp m hm
    by_contra h
    have hs : ↑m.support ⊆ Set.range f := by
      intro i hi
      refine ⟨⟨i, ?_⟩, rfl⟩
      intro hiT
      exact h ⟨i, hiT, Finsupp.mem_support_iff.mp hi⟩
    have hc := congrArg (fun r : MvPolynomial {i : Fin n // i ∉ T} R =>
      r.coeff (m.comapDomain f hf.injOn)) hp
    rw [MvPolynomial.coeff_killCompl,
      Finsupp.mapDomain_comapDomain f hf m hs, AddMonoidAlgebra.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  · intro hp
    ext m
    rw [MvPolynomial.coeff_killCompl, AddMonoidAlgebra.coeff_zero]
    by_contra h
    obtain ⟨i, hiT, hi⟩ := hp _ (MvPolynomial.mem_support_iff.mpr h)
    have hs := Finsupp.mapDomain_support (f := f) (s := m)
      (Finsupp.mem_support_iff.mpr hi)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hs
    subst i
    exact j.property hiT

/-- The integral projective morphism inserting zeros outside the retained coordinates.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_integralCoordinateInclusion {ι κ : Type} (e : κ ↪ ι) :
    Proj (homogeneousSubmodule κ (ULift.{0} ℤ)) ⟶
      Proj (homogeneousSubmodule ι (ULift.{0} ℤ)) :=
  Proj.map (s2e_gradedCoordinateProjection e)
    (s2e_irrelevant_le_map_of_graded_retraction _ _
      (s2e_gradedCoordinateProjection e) (s2e_gradedCoordinateSection e)
      (s2e_gradedCoordinate_retraction e))

/-- The retained-coordinate morphism is a scheme closed immersion.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_integralCoordinateInclusion_isClosedImmersion {ι κ : Type} (e : κ ↪ ι) :
    IsClosedImmersion (s2e_integralCoordinateInclusion e) := by
  exact s2e_proj_map_isClosedImmersion_of_graded_retraction _ _
    (s2e_gradedCoordinateProjection e) (s2e_gradedCoordinateSection e)
    (s2e_gradedCoordinate_retraction e) _

/-- The integral coordinate subspace has exactly the selected homogeneous coordinates zero.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_integralCoordinateInclusion_range (k : ℕ) (T : Finset (Fin (k + 1))) :
    Set.range (s2e_integralCoordinateInclusion
      (⟨Subtype.val, Subtype.val_injective⟩ : {j : Fin (k + 1) // j ∉ T} ↪ Fin (k + 1))) =
      {p | ∀ j ∈ T, (X j : MvPolynomial (Fin (k + 1)) (ULift.{0} ℤ)) ∈
        p.asHomogeneousIdeal.toIdeal} := by
  let e : {j : Fin (k + 1) // j ∉ T} ↪ Fin (k + 1) := ⟨Subtype.val, Subtype.val_injective⟩
  change Set.range (Proj.map (s2e_gradedCoordinateProjection e) _) = _
  rw [s2e_proj_map_range_of_graded_retraction _ _ (s2e_gradedCoordinateProjection e)
    (s2e_gradedCoordinateSection e) (s2e_gradedCoordinate_retraction e)]
  have hk : RingHom.ker (s2e_gradedCoordinateProjection e).toRingHom =
      Ideal.span ((X (R := ULift.{0} ℤ)) '' (↑T : Set (Fin (k + 1)))) :=
    s2e_polynomial_coordinate_kernel (ULift.{0} ℤ) (k + 1) T
  rw [hk]
  ext p
  change Ideal.span ((X (R := ULift.{0} ℤ)) '' (↑T : Set (Fin (k + 1)))) ≤
    p.asHomogeneousIdeal.toIdeal ↔ _
  rw [Ideal.span_le]
  constructor
  · intro h j hj
    exact h ⟨j, hj, rfl⟩
  · intro h a ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact h j hj

end HodgeLean.Foundations.Program

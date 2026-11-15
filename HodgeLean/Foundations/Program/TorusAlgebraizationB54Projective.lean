import HodgeLean.Foundations.Program.TorusAlgebraizationB54Presentation
import HodgeLean.Foundations.Program.TorusAlgebraizationB54RelativeProj
import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (G : ℕ → Submodule R A) [GradedRing G]

def b54_integralGradedCoordinates (v : ι → A) (hv : ∀ i, v i ∈ G 1) :
    homogeneousSubmodule ι (ULift.{0} ℤ) →+*ᵍ G :=
  { eval₂Hom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) v with
    map_mem := b54_eval₂_mem_grade G _ (by
      intro c
      change (c.down : A) ∈ G 0
      have h := map_intCast (algebraMap (G 0) A) c.down
      rw [← h]
      exact (c.down : G 0).property) v hv }

@[simp] theorem b54_integralGradedCoordinates_X (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (i : ι) : b54_integralGradedCoordinates G v hv (X i) = v i := by
  simp [b54_integralGradedCoordinates]

theorem b54_integralCoordinates_irrelevant [Fintype ι]
    (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤) :
    HomogeneousIdeal.irrelevant G ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι (ULift.{0} ℤ))).map
        (b54_integralGradedCoordinates G v hv) := by
  apply (b54_irrelevant_le_span_generators G v hv hgen).trans
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  rw [← b54_integralGradedCoordinates_X G v hv i]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _
    zero_lt_one (isHomogeneous_X _ i))

theorem b54_polynomial_irrelevant_le_variables (ι C : Type) [CommRing C] :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι C)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : ι → MvPolynomial ι C)) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨d, hd, hp⟩ := hp
  have hpow : p ∈ Ideal.span (Set.range (MvPolynomial.X : ι → MvPolynomial ι C)) ^ d := by
    rw [Ideal.span_pow_eq_map_homogeneousSubmodule]
    exact ⟨MvPolynomial.map MvPolynomial.C p, hp.map _, by simp⟩
  exact Ideal.pow_le_self hd.ne' hpow

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def b54_projectivePresentation [Algebra R (G 0)]
    (hscalar : Function.Bijective (algebraMap R (G 0)))
    (n : ℕ) (v : Fin (n + 1) → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤) :
    ProjectiveSpace.Presentation (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap R (G 0)))) := by
  let f := b54_integralGradedCoordinates G v hv
  let hf := b54_integralCoordinates_irrelevant G v hv hgen
  let j₀ := b54_relativeProj f hf
  have hj₀ : IsClosedImmersion j₀ := by
    apply b54_relativeProj_isClosedImmersion f hf X (isHomogeneous_X _)
      (b54_polynomial_irrelevant_le_variables _ _)
    simpa [f] using hgen
  let c := Spec.map (CommRingCat.ofHom (algebraMap R (G 0)))
  have : IsIso (CommRingCat.ofHom (algebraMap R (G 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hscalar
  have hc : IsIso c := by dsimp [c]; infer_instance
  let e : pullback (terminal.from (Spec (.of (G 0))))
      (terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)))) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec (.of R)) :=
    pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsIso e := by dsimp [e, c]; infer_instance
  let j := j₀ ≫ e
  have : IsClosedImmersion j := by dsimp [j]; infer_instance
  refine ⟨n, j, ?_⟩
  simp [j, j₀, e, c, b54_relativeProj, ProjectiveSpace.toBase, Category.assoc]

theorem b54_projective_of_degree_one [Algebra R (G 0)]
    (hscalar : Function.Bijective (algebraMap R (G 0)))
    (n : ℕ) (v : Fin (n + 1) → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤) :
    IsProjective (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom (algebraMap R (G 0)))) :=
  ⟨⟨b54_projectivePresentation G hscalar n v hv hgen⟩⟩

end HodgeLean.Foundations.Program

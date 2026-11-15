import HodgeLean.Foundations.Program.SchoenInvariantAffineNeighborhoods
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finite families of Proj points have a common affine basic open when they each
miss an element of one fixed positive degree over an infinite field. -/
theorem s2_proj_commonAffineOpen
    (K A : Type*) [Field K] [Infinite K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    (ι : Type*) [Finite ι] (x : ι → Proj 𝒜) (d : ℕ) (hd : 0 < d)
    (hx : ∀ i, ∃ a : 𝒜 d, (a : A) ∉ (x i).asHomogeneousIdeal) :
    ∃ f : A, f ∈ 𝒜 d ∧ IsAffineOpen (Proj.basicOpen 𝒜 f) ∧
      ∀ i, x i ∈ Proj.basicOpen 𝒜 f := by
  let p (i : ι) : Submodule K (𝒜 d) :=
    ((x i).asHomogeneousIdeal.toIdeal.restrictScalars K).comap (𝒜 d).subtype
  have hp (i : ι) : p i ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hx i
    intro he
    have hm : a ∈ p i := he ▸ Submodule.mem_top
    exact ha hm
  obtain ⟨f, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨f, f.property, Proj.isAffineOpen_basicOpen 𝒜 (f : A) f.property hd, ?_⟩
  intro i
  exact hf i

/-- A positive graded piece generating the irrelevant ideal supplies common
 affine neighborhoods for every finite family of Proj points. -/
theorem s2_proj_commonAffineOpen_of_irrelevant_le_span
    (K A : Type*) [Field K] [Infinite K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    (d : ℕ) (hd : 0 < d)
    (hgen : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (𝒜 d : Set A))
    (ι : Type*) [Finite ι] (x : ι → Proj 𝒜) :
    ∃ f : A, f ∈ 𝒜 d ∧ IsAffineOpen (Proj.basicOpen 𝒜 f) ∧
      ∀ i, x i ∈ Proj.basicOpen 𝒜 f := by
  apply s2_proj_commonAffineOpen K A 𝒜 ι x d hd
  intro i
  by_contra! h
  apply (x i).not_irrelevant_le
  have hspan : Ideal.span (𝒜 d : Set A) ≤ (x i).asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    intro a ha
    exact h ⟨a, ha⟩
  exact hgen.trans hspan

/-- Degree one generates an ideal containing every positive homogeneous polynomial. -/
theorem s2_mvPolynomial_irrelevant_le_span_degreeOne
    (K σ : Type*) [Field K] :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (MvPolynomial.homogeneousSubmodule σ K 1 : Set (MvPolynomial σ K)) := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  rw [HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro f hf
  obtain ⟨d, hf⟩ := Set.mem_iUnion.mp hf
  obtain ⟨hd, hf⟩ := Set.mem_iUnion.mp hf
  have hvars : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) ≤
      Ideal.span (MvPolynomial.homogeneousSubmodule σ K 1 : Set (MvPolynomial σ K)) := by
    apply Ideal.span_mono
    rintro _ ⟨j, rfl⟩
    exact MvPolynomial.isHomogeneous_X K j
  apply hvars
  rw [← Set.image_univ]
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro m hm
  suffices ∃ j, m j ≠ 0 by simpa using this
  by_contra! h
  have hm0 : m = 0 := by ext j; exact h j
  subst m
  have hhom : f.IsHomogeneous d := hf
  have hz := hhom.coeff_eq_zero (show (0 : σ →₀ ℕ).degree ≠ d by simpa using hd.ne)
  exact (MvPolynomial.mem_support_iff.mp hm) hz

/-- Finite families of points in polynomial Proj over an infinite field have a
common affine open defined by a degree-one polynomial. -/
theorem s2_polynomialProj_commonAffineOpen (K σ : Type*) [Field K] [Infinite K]
    (ι : Type*) [Finite ι] :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
    ∀ x : ι → Proj (MvPolynomial.homogeneousSubmodule σ K),
      ∃ f : MvPolynomial σ K, f.IsHomogeneous 1 ∧
        IsAffineOpen (Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) f) ∧
        ∀ i, x i ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) f := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  intro x
  exact s2_proj_commonAffineOpen_of_irrelevant_le_span K (MvPolynomial σ K)
    (MvPolynomial.homogeneousSubmodule σ K) 1 Nat.zero_lt_one
    (s2_mvPolynomial_irrelevant_le_span_degreeOne K σ) ι x

/-- Common affine neighborhoods pull back along affine morphisms into polynomial Proj. -/
theorem s2_affineHom_polynomialProj_commonAffineOpen
    (K σ : Type*) [Field K] [Infinite K] (X : Scheme)
    (ι : Type*) [Finite ι] (x : ι → X) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
    ∀ f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K),
      IsAffineHom f → ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  intro f hf
  letI := hf
  obtain ⟨a, _, ha, hmem⟩ := s2_polynomialProj_commonAffineOpen K σ ι (fun i => f (x i))
  exact ⟨f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) a,
    ha.preimage f, hmem⟩

/-- An affine map to polynomial Proj supplies invariant affine neighborhoods
for finite scheme actions when the source has affine diagonal. -/
theorem s2_polynomialProj_invariantAffineNeighborhood
    (K σ : Type*) [Field K] [Infinite K] (X : Scheme)
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* CategoryTheory.Aut X) (x : X) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
    ∀ f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K), IsAffineHom f →
      ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
        ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  intro f hf
  obtain ⟨V, hV, hx⟩ := s2_affineHom_polynomialProj_commonAffineOpen K σ X G
    (fun g => (ρ g).asIso.hom x) f hf
  obtain ⟨U, hU, hxU, _, hinv⟩ := s2_invariantAffineNeighborhood X G ρ V hV x hx
  exact ⟨U, hU, hxU, hinv⟩

end HodgeLean.Foundations.Program

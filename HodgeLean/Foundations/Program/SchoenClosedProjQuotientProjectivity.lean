import HodgeLean.Foundations.Program.SchoenEquivariantClosedProjBase
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientCoefficientEquiv
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientFiniteType
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientScalarGrading
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientDegreeZero
import HodgeLean.Foundations.Program.SchoenGluedProjCoefficientProjectivity
import HodgeLean.Foundations.Program.SchoenGluedQuotientEquivariantIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual equivariant closed Proj presentation over a coefficient field gives a projective glued finite-action quotient. -/
theorem s2_closedProjQuotient_projective {K A G : Type} [Field K] [Infinite K]
    [CommRing A] [Algebra K A] [Group G] [Fintype G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    [Algebra.FiniteType (𝒜 0) A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hK : ∀ n, ∀ k : K, ∀ a ∈ 𝒜 n, k • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a)
    (eA : 𝒜 0 ≃+* K) (X : Scheme.{0}) [IsIntegral X]
    [IsSeparated (terminal.from X)] (ρ : G →* Aut X)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (s : X ⟶ Spec (.of K)) (hs : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (f : X ⟶ Proj 𝒜) [IsClosedImmersion f]
    (he : ∀ g : G, (ρ g).asIso.hom ≫ f = f ≫ (s2_projAction 𝒜 hgrade g).asIso.hom)
    (hbase : f ≫ Proj.toSpecZero 𝒜 ≫ Spec.map eA.symm.toCommRingCatIso.hom = s) :
    IsProjective (s2_gluedQuotientStructure s G ρ hs hcover) := by
  let p : ProjectiveSpectrum 𝒜 := f (genericPoint X)
  let I := p.asHomogeneousIdeal
  have hI : ∀ g : G, ∀ a ∈ I.toIdeal, g • a ∈ I.toIdeal :=
    s2_fixedProjPoint_ideal_invariant 𝒜 hgrade p
      (s2_equivariantProj_genericImage_fixed 𝒜 hgrade X ρ f he)
  letI := s2_homogeneousQuotientGrading 𝒜 I
  letI := s2_quotientRingAction I.toIdeal hI
  haveI : I.toIdeal.IsPrime := p.isPrime
  let ℬ := s2_homogeneousQuotientPiece 𝒜 I
  let hg := s2_homogeneousQuotientAction_preserves_grading 𝒜 hgrade I hI
  let hk := s2_homogeneousQuotient_scalar_grading 𝒜 hK I
  let hz := s2_homogeneousQuotientAction_fixes_degreeZero 𝒜 I hI hzero
  let eB := s2_homogeneousQuotientCoefficientEquiv 𝒜 I eA
  haveI : IsNoetherianRing (ℬ 0) := s2_homogeneousQuotient_degreeZero_noetherian 𝒜 I
  haveI : Algebra.FiniteType (ℬ 0) (A ⧸ I.toIdeal) := s2_homogeneousQuotient_finiteType 𝒜 I
  obtain ⟨e, hf, hb, heq⟩ := s2_equivariantClosedProj_presentation_over 𝒜 hgrade X
    (Spec (.of K)) ρ f he (Spec.map eA.symm.toCommRingCatIso.hom) s hbase
  haveI : IsIntegral (Proj ℬ) := IsIntegral.of_isIso e.hom
  haveI : IsSeparated (terminal.from (Proj ℬ)) := by
    rw [← terminal.comp_from e.inv]
    infer_instance
  let t := Proj.toSpecZero ℬ ≫ Spec.map eB.symm.toCommRingCatIso.hom
  have ht : ∀ g : G, (s2_projAction ℬ hg g).asIso.hom ≫ t = t := by
    intro g
    dsimp only [t]
    rw [← Category.assoc, s2_projAction_toSpecZero ℬ hg hk hz]
  have hbet : e.hom ≫ t = s := by
    dsimp only [t]
    have hc : Spec.map eB.symm.toCommRingCatIso.hom =
        Spec.map (CommRingCat.ofHom (s2_homogeneousQuotientZeroMap 𝒜 I)) ≫
          Spec.map eA.symm.toCommRingCatIso.hom := by
      rw [← Spec.map_comp]
      rfl
    rw [hc]
    exact hb
  haveI : IsProjective (s2_gluedQuotientStructure t G (s2_projAction ℬ hg) ht
      (s2_proj_invariantAffineCover ℬ hg hk)) :=
    s2_gluedProjQuotient_projective_coefficientField ℬ hg hk hz eB ht
  exact s2_gluedQuotient_projective_of_equivariantIso G ρ (s2_projAction ℬ hg)
    hcover (s2_proj_invariantAffineCover ℬ hg hk) e heq s t hbet hs ht

end HodgeLean.Foundations.Program

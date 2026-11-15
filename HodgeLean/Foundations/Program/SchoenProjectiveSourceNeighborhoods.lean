import HodgeLean.Foundations.Program.SchoenIntegerProjectiveNeighborhoods
import HodgeLean.Foundations.Program.SchoenProjStructurePoints

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An affine map to integer polynomial Proj supplies common affine neighborhoods
on any scheme over a characteristic-zero field. -/
theorem s2_integerPolynomialProj_source_commonAffineOpen
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) (ι : Type) [Finite ι] (x : ι → X) :
    letI := MvPolynomial.gradedAlgebra (σ := Fin n) (R := ULift.{0} ℤ)
    ∀ f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin n) (ULift.{0} ℤ)),
      IsAffineHom f → ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin n) (R := ULift.{0} ℤ)
  intro f hf
  letI := hf
  let φ : ULift.{0} ℤ →+* K := (Int.castRingHom K).comp ULift.ringEquiv.toRingHom
  have hφ : Function.Injective φ := Int.cast_injective.comp ULift.ringEquiv.injective
  have hcomm : f ≫ s2_polynomialProj_toBaseRing (ULift.{0} ℤ) (Fin n) =
      s ≫ Spec.map (CommRingCat.ofHom φ) := specULiftZIsTerminal.hom_ext _ _
  have hinj := s2_polynomialProj_constants_injective_of_structure
    (ULift.{0} ℤ) K (Fin n) φ hφ X s f hcomm
  obtain ⟨a, _, ha, hmem⟩ := s2_polynomialProj_commonAffineOpen_of_constants_injective
    (ULift.{0} ℤ) n ι (fun i => f (x i)) (fun i => hinj (x i))
  exact ⟨f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) (ULift.{0} ℤ)) a,
    ha.preimage f, hmem⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite families on a projective scheme over a characteristic-zero field have
one common affine open neighborhood. -/
theorem s2_projective_commonAffineOpen
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (ι : Type) [Finite ι] (x : ι → X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := s)
  letI := P.isClosedImmersion
  letI := MvPolynomial.gradedAlgebra (σ := Fin (P.ambientDimension + 1)) (R := ULift.{0} ℤ)
  let Z := Proj (MvPolynomial.homogeneousSubmodule (Fin (P.ambientDimension + 1)) (ULift.{0} ℤ))
  let f : X ⟶ Z := P.immersion ≫ pullback.snd (terminal.from (Spec (CommRingCat.of K)))
    (terminal.from Z)
  haveI : IsAffine (terminal (Scheme.{0})) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).inv
  haveI : IsAffineHom P.immersion := inferInstance
  haveI : IsAffineHom (terminal.from (Spec (CommRingCat.of K))) := inferInstance
  haveI : IsAffineHom (pullback.snd (terminal.from (Spec (CommRingCat.of K)))
      (terminal.from Z)) := MorphismProperty.pullback_snd _ _ inferInstance
  have hf : IsAffineHom f := by
    dsimp only [f]
    exact MorphismProperty.comp_mem (@IsAffineHom) _ _ inferInstance inferInstance
  exact s2_integerPolynomialProj_source_commonAffineOpen K X s
    (P.ambientDimension + 1) ι x f hf

/-- A finite scheme action on a projective characteristic-zero scheme has
invariant affine neighborhoods at every point. -/
theorem s2_projective_invariantAffineNeighborhood
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U := by
  obtain ⟨V, hV, hx⟩ := s2_projective_commonAffineOpen K X s G
    (fun g => (ρ g).asIso.hom x)
  haveI : IsAffine (terminal (Scheme.{0})) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).inv
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from s]
    infer_instance
  obtain ⟨U, hU, hxU, _, hinv⟩ := s2_invariantAffineNeighborhood X G ρ V hV x hx
  exact ⟨U, hU, hxU, hinv⟩

end HodgeLean.Foundations.Program

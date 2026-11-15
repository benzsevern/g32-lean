import HodgeLean.Foundations.Program.SchoenCycleComplexFixedFunctionLocalPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual localized fixed-function pullback sends every original fixed section to its actual geometric germ.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_fixed_function_local_pullback_of
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ g, a g ≫ q = q) (U : Y.left.Opens)
    (hW : IsAffineOpen (q.left ⁻¹ᵁ U)) (p : X.left) (hp : p ∈ q.left ⁻¹ᵁ U)
    (hfix : ∀ g, (a g).left p = p) :
    let W := q.left ⁻¹ᵁ U
    letI := s2e_step1_sectionAlgebra X W
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
    let S := FixedPoints.subalgebra ℂ Γ(X.left, W) G
    let Q := P.comap S.val.toRingHom
    let R := X.left.presheaf.stalk p
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    ∀ s : S, s2e_complex_fixed_function_local_pullback X Y G a ha1 hamul q hinv U hW p hp hfix
      (algebraMap S (Localization.AtPrime Q) s) = (X.left.presheaf.germ W p hp).hom s.val := by
  dsimp only
  let W := q.left ⁻¹ᵁ U
  let C := Γ(X.left, W)
  let R := X.left.presheaf.stalk p
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  letI : Nonempty W := ⟨⟨p, hp⟩⟩
  letI : Algebra C R := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨p, hp⟩
  letI : IsScalarTower ℂ C R := IsScalarTower.of_algebraMap_eq
    (fun c => ((s2e_complex_section_germ X W p hp).commutes c).symm)
  let P := (hW.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : IsLocalization.AtPrime R P := hW.isLocalization_stalk ⟨p, hp⟩
  intro s
  change s2e_fixed_prime_localization_map ℂ C R G P _ = _
  exact s2e_fixed_prime_localization_map_of ℂ C R G P s

#print axioms s2e_complex_fixed_function_local_pullback_of
end HodgeLean.Foundations.Program

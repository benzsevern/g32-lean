import HodgeLean.Foundations.Program.SchoenTowerN2bNormalizedEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Retaining the affine embedding coordinates makes the normalized projective chart map an immersion. -/
theorem g32l4_normalized_projective_chart_immersion
    {X S : Scheme.{0}} (s : X ⟶ S) {κ : Type}
    (q : ULift.{0} ℤ →+* Γ(X, ⊤)) (a : κ → Γ(X, ⊤))
    (k : κ) (hk : a k = 1) (m : ℕ) (v : Fin m → Γ(X, ⊤))
    [IsClosedImmersion (AffineSpace.homOfVector s v)]
    (t : Fin m → κ) (ht : ∀ i, a (t i) = v i) :
    IsImmersion (pullback.lift s
      (Proj.fromOfGlobalSections (X := X) (homogeneousSubmodule κ (ULift.{0} ℤ))
        (eval₂Hom q a) (n2b_polynomial_evaluation_irrelevant q a k hk))
      (show s ≫ terminal.from _ = _ ≫ terminal.from _ from Subsingleton.elim _ _) :
      X ⟶ ProjectiveSpace κ (S)) := by
  let 𝒜 := homogeneousSubmodule κ (ULift.{0} ℤ)
  let φ := eval₂Hom q a
  have hφ : φ (MvPolynomial.X k) = 1 := by rw [eval₂Hom_X', hk]
  let L := Away 𝒜 (MvPolynomial.X k)
  let F : X ⟶ Spec (CommRingCat.of L) := X.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (s2_normalizedChartLift 𝒜 (MvPolynomial.X k) φ hφ))
  let P := pullback (terminal.from (S)) (terminal.from (Spec (CommRingCat.of L)))
  let f : X ⟶ P := pullback.lift s F (Subsingleton.elim _ _)
  let w : Fin m → Γ(P, ⊤) := fun i =>
    (pullback.snd (terminal.from (S)) (terminal.from (Spec (CommRingCat.of L)))).appTop.hom
      ((Scheme.ΓSpecIso _).inv.hom
        (Away.mk 𝒜 (isHomogeneous_X _ k) 1 (MvPolynomial.X (t i))
          (by simpa only [𝒜, one_smul, mem_homogeneousSubmodule] using isHomogeneous_X (ULift.{0} ℤ) (t i))))
  let H : P ⟶ AffineSpace (Fin m) (S) := AffineSpace.homOfVector (pullback.fst _ _) w
  have hfH : f ≫ H = AffineSpace.homOfVector s v := by
    rw [AffineSpace.comp_homOfVector, pullback.lift_fst]
    congr 1
    funext i
    change f.appTop.hom (w i) = v i
    dsimp only [w]
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, pullback.lift_snd]
    exact (n2b_normalized_coordinate_evaluation X q a k hk (t i)).trans (ht i)
  haveI : IsImmersion (f ≫ H) := by rw [hfH]; infer_instance
  haveI : IsImmersion f := IsImmersion.of_comp f H
  let j : P ⟶ ProjectiveSpace κ (S) :=
    pullback.map _ _ _ _ (𝟙 _) (Proj.awayι 𝒜 (MvPolynomial.X k) (isHomogeneous_X _ k) zero_lt_one)
      (𝟙 _) (by simp) (Subsingleton.elim _ _)
  haveI : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hfj : f ≫ j = pullback.lift s
      (Proj.fromOfGlobalSections (X := X) 𝒜 φ
        (n2b_polynomial_evaluation_irrelevant q a k hk)) (Subsingleton.elim _ _) := by
    apply pullback.hom_ext
    · simp only [j, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id, f, pullback.lift_fst]
    · simp only [j, Category.assoc, pullback.map, pullback.lift_snd, f, pullback.lift_snd_assoc,
        pullback.lift_snd]
      exact (s2_fromGlobalSections_normalizedChart 𝒜 X φ
        (n2b_polynomial_evaluation_irrelevant q a k hk) (isHomogeneous_X _ k) zero_lt_one hφ).symm
  rw [← hfj]
  infer_instance

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenCycleNativeSectionGerms
import Mathlib.RingTheory.Localization.Defs

/-! # Actual algebraic stalks realized in the native analytic germ ring -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- The actual algebraic stalk maps to analytic germs by localizing regular section germs on an affine neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
def s2e_nativeStalkGermHom
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.affineOpens) (hp : p.underlying ∈ U.1) :
    X.left.presheaf.stalk p.underlying →+* AnalyticGermAt d 0 := by
  letI : Algebra Γ(X.left, U.1) (X.left.presheaf.stalk p.underlying) :=
    (X.left.presheaf.germ U.1 p.underlying hp).hom.toAlgebra
  letI := U.2.isLocalization_stalk ⟨p.underlying, hp⟩
  exact IsLocalization.lift (S := X.left.presheaf.stalk p.underlying)
    (s2e_nativeSectionGermHom_primeCompl_units X d p U hp)

/-- The actual stalk realization agrees with the analytic germ of every section on its chosen affine neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeStalkGermHom_germ
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.affineOpens) (hp : p.underlying ∈ U.1)
    (s : Γ(X.left, U.1)) :
    s2e_nativeStalkGermHom X d p U hp (X.left.presheaf.germ U.1 p.underlying hp s) =
      s2e_nativeSectionGermHom X d p U.1 hp s := by
  letI : Algebra Γ(X.left, U.1) (X.left.presheaf.stalk p.underlying) :=
    (X.left.presheaf.germ U.1 p.underlying hp).hom.toAlgebra
  letI := U.2.isLocalization_stalk ⟨p.underlying, hp⟩
  unfold s2e_nativeStalkGermHom
  exact IsLocalization.lift_eq _ s

/-- The analytic realization of an algebraic stalk is unchanged on an affine refinement.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeStalkGermHom_refine
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U V : X.left.affineOpens) (hpU : p.underlying ∈ U.1)
    (hpV : p.underlying ∈ V.1) (hVU : V ≤ U) :
    s2e_nativeStalkGermHom X d p U hpU = s2e_nativeStalkGermHom X d p V hpV := by
  letI : Algebra Γ(X.left, U.1) (X.left.presheaf.stalk p.underlying) :=
    (X.left.presheaf.germ U.1 p.underlying hpU).hom.toAlgebra
  letI := U.2.isLocalization_stalk ⟨p.underlying, hpU⟩
  apply IsLocalization.ringHom_ext (M := (U.2.primeIdealOf ⟨p.underlying, hpU⟩).asIdeal.primeCompl)
  apply RingHom.ext
  intro s
  change s2e_nativeStalkGermHom X d p U hpU
    (X.left.presheaf.germ U.1 p.underlying hpU s) =
      s2e_nativeStalkGermHom X d p V hpV
        (X.left.presheaf.germ U.1 p.underlying hpU s)
  rw [s2e_nativeStalkGermHom_germ X d p U hpU s]
  have hgs : X.left.presheaf.germ U.1 p.underlying hpU s =
      X.left.presheaf.germ V.1 p.underlying hpV
        (X.left.presheaf.map (homOfLE hVU).op s) := by
    exact (X.left.presheaf.germ_res_apply
      (homOfLE (show V.1 ≤ U.1 from hVU)) p.underlying hpV s).symm
  rw [hgs, s2e_nativeStalkGermHom_germ]
  exact (s2e_nativeSectionGermHom_restrict X d p U.1 V.1 hpU hpV hVU s).symm

/-- The localized native stalk map realizes sections from every actual open neighbourhood, not only its chosen affine chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Serre, Géométrie algébrique et géométrie analytique, §2, printed pp. 9–11. -/
theorem s2e_nativeStalkGermHom_germ_on_open
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.affineOpens) (hpU : p.underlying ∈ U.1)
    (V : X.left.Opens) (hpV : p.underlying ∈ V) (s : Γ(X.left, V)) :
    s2e_nativeStalkGermHom X d p U hpU (X.left.presheaf.germ V p.underlying hpV s) =
      s2e_nativeSectionGermHom X d p V hpV s := by
  obtain ⟨W, hW, hpW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show p.underlying ∈ U.1 ⊓ V from ⟨hpU, hpV⟩)
  have hWU : (⟨W, hW⟩ : X.left.affineOpens) ≤ U := fun _ h => (hsub h).1
  have hWV : W ≤ V := fun _ h => (hsub h).2
  rw [s2e_nativeStalkGermHom_refine X d p U ⟨W, hW⟩ hpU hpW hWU]
  have hgs : X.left.presheaf.germ V p.underlying hpV s =
      X.left.presheaf.germ W p.underlying hpW
        (X.left.presheaf.map (homOfLE hWV).op s) := by
    change (X.left.presheaf.germ V p.underlying hpV).hom s =
      (X.left.presheaf.map (homOfLE hWV).op ≫
        X.left.presheaf.germ W p.underlying hpW).hom s
    rw [X.left.presheaf.germ_res]
  rw [hgs, s2e_nativeStalkGermHom_germ]
  exact s2e_nativeSectionGermHom_restrict X d p V W hpV hpW hWV s

end HodgeLean.Foundations.Program

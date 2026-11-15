import HodgeLean.Foundations.Analytic.AnalytificationChow3Charts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry ProjectiveSpace
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

theorem n2b_projective_of_affine_proper {X S : Scheme.{0}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsProper f] : IsProjective f := by
  obtain ⟨n, φ, hφ, hφf⟩ := AnalytificationChow3_exists_immersion
    f (𝟙 S) f (Category.comp_id f) ⊤ (isAffineOpen_top X)
  let i := X.topIso.inv ≫ φ
  haveI : IsImmersion φ := hφ
  haveI : IsImmersion i := by dsimp only [i]; infer_instance
  have hi : i ≫ toBase (Fin (n + 1)) S = f := by
    dsimp only [i]
    rw [Category.assoc, hφf, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  haveI : IsProper (i ≫ toBase (Fin (n + 1)) S) := by rw [hi]; infer_instance
  haveI : IsProper i := IsProper.of_comp i (toBase (Fin (n + 1)) S)
  haveI : IsClosedImmersion i :=
    IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range
  exact ⟨⟨⟨n, i, hi⟩⟩⟩

theorem n2b_projective_of_finite_affine_base {X S : Scheme.{0}}
    [IsAffine S] (f : X ⟶ S) [IsFinite f] : IsProjective f := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  exact n2b_projective_of_affine_proper f

theorem n2b_projective_finite_on_affine_open {X S : Scheme.{0}}
    (f : X ⟶ S) [IsFinite f] (U : S.affineOpens) :
    IsProjective (f ∣_ U.1) := by
  exact n2b_projective_of_finite_affine_base (f ∣_ U.1)

end HodgeLean.Foundations.Program

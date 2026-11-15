import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNQuotientNativeMap
import HodgeLean.Foundations.Program.G32Native.PairedC3PolynomialSliceRelation
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonCompositionIso

/-! # The natural source-to-total comparison on an original Rees chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- On the binomial Rees chart the original source-to-total ideal comparison
is invertible when the restricted branch parameter is regular. The map
is the native comparison of the actual quotient spectra.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_rees_native_ideal_comparison
    {A : Type} [CommRing A] (I : Ideal A) (u v a : A)
    (ha : u - a * v ∈ I) (hv : IsSMulRegular (A ⧸ I) v) :
    let r : A[X] := C u - X * C v
    let B := A[X] ⧸ Ideal.span {r}
    let J := (I.map (C : A →+* A[X])).map (algebraMap A[X] B)
    let i₀ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let i₁ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let σ := Spec.map (CommRingCat.ofHom (algebraMap A[X] B)) ≫
      Spec.map (CommRingCat.ofHom (C : A →+* A[X]))
    ∃ (g : Spec (CommRingCat.of (B ⧸ J)) ⟶ Spec (CommRingCat.of (A ⧸ I)))
      (h : g ≫ i₀ = i₁ ≫ σ),
      IsIso (Conormal.idealPullbackMap i₀ i₁ σ g h) ∧
        IsIso (Conormal.comparisonMap i₀ i₁ σ g h) := by
  dsimp only
  let P := A[X]
  let K : Ideal P := I.map C
  let r : P := C u - X * C v
  let B := P ⧸ Ideal.span {r}
  let J := K.map (algebraMap P B)
  let i₀ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let iP := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  let i₁ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A P))
  let f₁ := Spec.map (CommRingCat.ofHom (algebraMap P B))
  let g₀ := Conormal.quotientBaseChangeMap (S := P) I
  let g₁ := Conormal.quotientBaseChangeMap (S := B) K
  have h₀ : g₀ ≫ i₀ = iP ≫ f₀ := Conormal.quotientBaseChangeMap_square (S := P) I
  have h₁ : g₁ ≫ iP = i₁ ≫ f₁ := Conormal.quotientBaseChangeMap_square (S := B) K
  haveI : IsIso (Conormal.idealPullbackMap i₀ iP f₀ g₀ h₀) :=
    Conormal.affineIdealPullbackMap_isIso_of_kernel_eq
      (CommRingCat.of (A ⧸ I)) (CommRingCat.of (P ⧸ K))
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom (Ideal.Quotient.mk K))
      (CommRingCat.ofHom (Ideal.quotientMap K (algebraMap A P) Ideal.le_comap_map)) h₀
      (by simp only [CommRingCat.hom_ofHom, Ideal.mk_ker]; rfl)
  haveI : IsIso (Conormal.idealPullbackMap iP i₁ f₁ g₁ h₁) :=
    paired_conormal_principal_quotient_ideal_map_isIso K r
      (paired_c3_polynomial_slice_relation_regular I u v a ha hv)
  have h : (g₁ ≫ g₀) ≫ i₀ = i₁ ≫ (f₁ ≫ f₀) := by
    rw [Category.assoc, h₀, ← Category.assoc, h₁, Category.assoc]
  haveI : IsIso (Conormal.idealPullbackMap i₀ i₁ (f₁ ≫ f₀) (g₁ ≫ g₀) h) :=
    Conormal.idealPullbackMap_comp_isIso i₀ iP i₁ f₀ f₁ g₀ g₁ h₀ h₁ h
  refine ⟨g₁ ≫ g₀, h, inferInstance, ?_⟩
  unfold Conormal.comparisonMap
  infer_instance

end HodgeLean.Foundations.Program.G32Native

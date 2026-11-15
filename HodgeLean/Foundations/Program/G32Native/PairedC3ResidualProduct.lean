import HodgeLean.Foundations.Program.G32Native.PairedResidualIntersection
import HodgeLean.Foundations.Program.G32Native.PairedResidualHyperplaneCriterion
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupProductRuling

/-! # The residual component over the centre–slice intersection

The inverse-image description below is scheme theoretic. It applies to the
actual exceptional ideal, without using a total-transform union identity.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The C3 residual ideal is the inverse image of the centre–slice intersection.
Source: Hartshorne, Algebraic Geometry, II.3, inverse images of closed subschemes;
II.7.13, the exceptional ideal of a blow-up. -/
theorem pairedC3_residual_ideal
    {X V Q : Scheme} (σ : V ⟶ X) (i₀ : Q ⟶ X)
    (K : X.IdealSheafData) :
    K.comap σ ⊔ i₀.ker.comap σ = (K ⊔ i₀.ker).comap σ :=
  (Scheme.IdealSheafData.comap_sup _ _ _).symm

/-- The residual component maps to the actual intersection in the penultimate
ambient scheme. This is the base projection before identifying its fibres.
Source: Hartshorne, Algebraic Geometry, II.3, scheme-theoretic inverse image. -/
def pairedC3ResidualBaseMap
    {base : Scheme} {V : Over base} {X Q : Scheme}
    (σ : V.left ⟶ X) (i₀ : Q ⟶ X) (K : X.IdealSheafData) :
    (residualComponent (V := V) (K.comap σ ⊔ i₀.ker.comap σ)).left ⟶
      (K ⊔ i₀.ker).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ σ
    (by rw [Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.comap_sup])

/-- The base projection retains its map to the full penultimate ambient scheme.
Source: Hartshorne, Algebraic Geometry, II.3, scheme-theoretic inverse image. -/
theorem pairedC3ResidualBaseMap_fac
    {base : Scheme} {V : Over base} {X Q : Scheme}
    (σ : V.left ⟶ X) (i₀ : Q ⟶ X) (K : X.IdealSheafData) :
    pairedC3ResidualBaseMap (V := V) σ i₀ K ≫ (K ⊔ i₀.ker).subschemeι =
      (residualComponentι (V := V) (K.comap σ ⊔ i₀.ker.comap σ)).left ≫ σ :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The actual residual component is the scheme-theoretic inverse image of
`D = K ∩ Q'`, rather than only having that underlying set.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem pairedC3ResidualBaseMap_isPullback
    {base : Scheme} {V : Over base} {X Q : Scheme}
    (σ : V.left ⟶ X) (i₀ : Q ⟶ X) (K : X.IdealSheafData) :
    IsPullback (pairedC3ResidualBaseMap (V := V) σ i₀ K)
      (residualComponentι (V := V) (K.comap σ ⊔ i₀.ker.comap σ)).left
      (K ⊔ i₀.ker).subschemeι σ := by
  apply (isPullback_of_isClosedImmersion _ _ _ _
    (pairedC3ResidualBaseMap_fac (V := V) σ i₀ K).symm ?_).flip
  change (K ⊔ i₀.ker).subschemeι.ker.comap σ =
    (K.comap σ ⊔ i₀.ker.comap σ).subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.comap_sup]

/-- Adding the total-transform ideal does not change the ideal cut out on the
retained slice. This uses its actual commuting square with the penultimate slice.
Source: Hartshorne, Algebraic Geometry, II.3; Schoen, Compositio Mathematica
65 (1988), Sublemma 2.7. -/
theorem pairedC3_residual_restriction
    {base : Scheme} {P V : Over base} (i : P ⟶ V)
    {X Q : Scheme} (σ : V.left ⟶ X) (i₀ : Q ⟶ X)
    (a : P.left ⟶ Q) (ha : i.left ≫ σ = a ≫ i₀)
    (K : X.IdealSheafData) :
    (K.comap σ ⊔ i₀.ker.comap σ).comap i.left = (K.comap σ).comap i.left := by
  have hzero : i₀.ker.comap (i.left ≫ σ) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    rw [Scheme.IdealSheafData.map_bot, ha]
    exact Scheme.Hom.le_ker_comp a i₀
  rw [Scheme.IdealSheafData.comap_sup,
    ← Scheme.IdealSheafData.comap_comp i₀.ker, hzero, sup_bot_eq]

#print axioms pairedC3_residual_ideal
#print axioms pairedC3ResidualBaseMap
#print axioms pairedC3ResidualBaseMap_fac
#print axioms pairedC3ResidualBaseMap_isPullback
#print axioms pairedC3_residual_restriction
end HodgeLean.Foundations.Program.G32Native

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine ideal pullback for the L1a comparison

Implication from affine scheme maps to the corresponding extension of ideals
on global sections. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Scheme ideal pullback on affine global sections is extension of ideals.
Source: Hartshorne, Algebraic Geometry, II.5, inverse images of ideal sheaves. -/
theorem s2v_l1a_affine_ideal_pullback
    {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (I : Y.IdealSheafData) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  have hpush (K : Ideal Γ(X, ⊤)) :
      ((Scheme.IdealSheafData.ofIdealTop K).map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
        K.comap f.appTop.hom := by
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    simp [Scheme.Hom.appTop]
    rfl
  have hrec (J : X.IdealSheafData) :
      Scheme.IdealSheafData.ofIdealTop (J.ideal ⟨⊤, isAffineOpen_top X⟩) = J := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp
  apply le_antisymm
  · let K := Ideal.map f.appTop.hom (I.ideal ⟨⊤, isAffineOpen_top Y⟩)
    have hle : I.comap f ≤ Scheme.IdealSheafData.ofIdealTop K := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [hpush]
      exact Ideal.le_comap_map
    simpa [K] using hle ⟨⊤, isAffineOpen_top X⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [← hpush, hrec]
    exact Scheme.IdealSheafData.le_map_comap I f ⟨⊤, isAffineOpen_top Y⟩

/-- Restriction along an open immersion preserves products of ideal sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and products of ideal sheaves. -/
theorem s2v_l1a_open_ideal_pullback_mul
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have he (K : Ideal Γ(Y, f ''ᵁ U.1)) :
      K.comap (f.appIso U.1).inv.hom = K.map (f.appIso U.1).hom.hom :=
    (Ideal.map_comap_of_equiv (f.appIso U.1).commRingCatIsoToRingEquiv).symm
  rw [he, he, he, Ideal.map_mul]

/-- Restriction along an open immersion preserves finite products of ideal sheaves.
Source: Hartshorne, Algebraic Geometry, II.5, restriction and products of ideal sheaves. -/
theorem s2v_l1a_open_ideal_pullback_prod
    {X Y : Scheme} {ι : Type*} (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ j ∈ s, I j).comap f = ∏ j ∈ s, (I j).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        s2v_l1a_open_ideal_pullback_mul, ih]

end HodgeLean.Foundations.Program

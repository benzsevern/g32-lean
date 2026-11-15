import HodgeLean.Foundations.Program.SchoenCycleAffineStalkAdic

/-! # Canonical adic maps of actual scheme stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual local stalk pullback induces a map of maximal-ideal adic rings.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms of locally ringed spaces. -/
def s2e_adic_stalkMap {X Y : Scheme} (f : X ⟶ Y) (p : X) :
    AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p))) (Y.presheaf.stalk (f p)) →+*
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) :=
  s2e_adic_ring_map _ _ (f.stalkMap p).hom (IsLocalRing.map_maximalIdeal_le (f.stalkMap p).hom)

#print axioms s2e_adic_stalkMap
/-- The actual adic stalk map commutes with affine pullback followed by germs.
Source: Hartshorne, Algebraic Geometry, II.2, compatibility of germs and pullback. -/
theorem s2e_adic_stalkMap_germ
    {X Y : Scheme} (f : X ⟶ Y) (p : X) (U : Y.Opens) (hp : f p ∈ U)
    (I : Ideal Γ(Y, U))
    (hd : I.map (Y.presheaf.germ U (f p) hp).hom ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (f p)))
    (hu : (I.map (f.app U).hom).map (X.presheaf.germ (f ⁻¹ᵁ U) p hp).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (z : AdicCompletion I Γ(Y, U)) :
    s2e_adic_stalkMap f p
      (s2e_adic_ring_map _ _ (Y.presheaf.germ U (f p) hp).hom hd z) =
    s2e_adic_ring_map _ _ (X.presheaf.germ (f ⁻¹ᵁ U) p hp).hom hu
      (s2e_adic_ring_map I _ (f.app U).hom le_rfl z) := by
  unfold s2e_adic_stalkMap
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2e_adic_ring_map_eval, s2e_adic_ring_map_eval,
    s2e_adic_ring_map_eval, s2e_adic_ring_map_eval]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n z)
  rw [← hr]
  change Ideal.Quotient.mk _ ((f.stalkMap p).hom ((Y.presheaf.germ U (f p) hp).hom r)) =
    Ideal.Quotient.mk _ ((X.presheaf.germ (f ⁻¹ᵁ U) p hp).hom ((f.app U).hom r))
  congr 1
  exact congrArg (fun k : Γ(Y, U) ⟶ X.presheaf.stalk p => k.hom r) (f.germ_stalkMap U p hp)

#print axioms s2e_adic_stalkMap_germ
/-- Actual adic stalk pullbacks respect composition of scheme morphisms.
Source: Hartshorne, Algebraic Geometry, II.2;
Mathlib, AlgebraicGeometry.Scheme.Hom.stalkMap_comp. -/
theorem s2e_adic_stalkMap_comp
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (z : AdicCompletion (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x))))
      (Z.presheaf.stalk (g (f x)))) :
    s2e_adic_stalkMap (f ≫ g) x z =
      s2e_adic_stalkMap f x (s2e_adic_stalkMap g (f x) z) := by
  unfold s2e_adic_stalkMap
  simp only [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact (s2e_adic_ring_map_comp _ _ _ (g.stalkMap (f x)).hom _
    (f.stalkMap x).hom _ _ z).symm

#print axioms s2e_adic_stalkMap_comp
end HodgeLean.Foundations.Program

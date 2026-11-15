import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedOpenCartier
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedPairCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual affine open base neighborhood supplies both Rees spectrum
charts in the retained stage, with their base squares and the specified point.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Scheme.exists_preimage_of_isPullback`. -/
theorem s2v_i2a_retained_pair_charts_over_open_base
    (Q : Scheme.{0}) (Y B : Over Q) [IsIntegral B.left] [IsLocallyNoetherian B.left]
    (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (huniv : ∀ (Z : Over Q) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    (R : Type) [CommRing R] [IsDomain R] (π : Spec (CommRingCat.of R) ⟶ Q)
    (c : Over.mk π ⟶ Y) [IsOpenImmersion c.left] (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hK : (K.comap c.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      (Ideal.span {x, y}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (p : B.left) (hp : b.left p ∈ Set.range c.left) :
    ∃ (gx : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ B.left)
      (gy : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {y, x}) y)) ⟶ B.left),
      IsOpenImmersion gx ∧ IsOpenImmersion gy ∧
      gx ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ c.left ∧
      gy ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ c.left ∧
      (p ∈ Set.range gx ∨ p ∈ Set.range gy) := by
  let P := pullback b c
  have hpb := (IsPullback.of_hasPullback b c).map (Over.forget Q)
  haveI : IsOpenImmersion (pullback.fst b c).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip (show IsOpenImmersion c.left from inferInstance)
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hqp, _⟩ := Scheme.exists_preimage_of_isPullback hpb p r hr.symm
  letI : Nonempty P.left := ⟨q⟩
  haveI : IsIntegral P.left := isIntegral_of_isOpenImmersion (pullback.fst b c).left
  haveI : IsLocallyNoetherian P.left :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst b c).left
  obtain ⟨gx, gy, hgx, hgy, hxb, hyb, hcover⟩ :=
    s2v_i2a_retained_pair_rees_charts Q R π P (pullback.snd b c) (K.comap c.left)
      (s2v_i2a_retained_cartier_universal_base_change Q Y B (Over.mk π) b c K huniv)
      (s2v_i2a_retained_open_base_change_cartier Q Y B (Over.mk π) b c K hcartier)
      x y hx hy hK
  letI : IsOpenImmersion gx := hgx
  letI : IsOpenImmersion gy := hgy
  have hsq : (pullback.fst b c).left ≫ b.left = (pullback.snd b c).left ≫ c.left :=
    congrArg (fun f => f.left) (pullback.condition (f := b) (g := c))
  refine ⟨gx ≫ (pullback.fst b c).left, gy ≫ (pullback.fst b c).left,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, hxb]
  · rw [Category.assoc, hsq, ← Category.assoc, hyb]
  · rcases hcover q with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact Or.inl ⟨z, (congrArg (pullback.fst b c).left hz).trans hqp⟩
    · exact Or.inr ⟨z, (congrArg (pullback.fst b c).left hz).trans hqp⟩

end HodgeLean.Foundations.Program

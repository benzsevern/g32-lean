import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedPairPointSupport
import HodgeLean.Foundations.Program.SchoenTowerI2aAffineSpectrumStructure

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every actual affine base chart supplies a retained paired point chart
with exact branch support, retaining both specified points and the scalar
structure through its canonical coefficient spectrum.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_affine_base_pair_point_exact_support
    (n : ℕ) (Y B U : Over (Spec ↧ℂ))
    [IsIntegral B.left] [IsLocallyNoetherian B.left] [IsAffine U.left] [IsIntegral U.left]
    (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (u₀ : U ⟶ Y) [IsOpenImmersion u₀.left]
    (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤)) (hc : c.Etale)
    (hcC : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (huniv : ∀ (Z : Over (Spec ↧ℂ)) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    {T : Type} [Fintype T] [DecidableEq T]
    (D : T → Y.left.IdealSheafData) (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n)
    (α β : J₀) (hαβ : α ≠ β)
    (hK : (K.comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {c (MvPolynomial.X (κ₀ α)), c (MvPolynomial.X (κ₀ β))})
    (hD : ∀ t : J₀, ((D t).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {c (MvPolynomial.X (κ₀ t))})
    (habsent : ∀ t, t ∉ J₀ → ((D t).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤)
    (x : ComplexPoint B) (hx : b.left x.underlying ∈ Set.range u₀.left)
    {L : Type} [Field L] (η : Spec (CommRingCat.of L) ⟶ B.left) [IsDominant η] :
    ∃ t₀ : J₀, (t₀ = α ∨ t₀ = β) ∧
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (u : V ⟶ B) (q : ComplexPoint V),
      IsOpenImmersion u.left ∧ Point.map u q = x ∧
      ∃ ηV : Spec (CommRingCat.of L) ⟶ V.left, ηV ≫ u.left = η ∧ IsDominant ηV ∧
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀.erase t₀ ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.underlying ∈ (s2c_strictTransform b.left (D t) K).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((s2c_strictTransform b.left (D t) K).comap u.left).ideal
          ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {z t}) := by
  classical
  let R := Γ(U.left, ⊤)
  letI : Algebra (MvPolynomial (Fin n) ℂ) R := c.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin n) ℂ) R := hc.toAlgebra
  let π := Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C))
  have hπ : π = U.left.isoSpec.inv ≫ U.hom :=
    s2v_i2a_affine_coordinate_spectrum_structure U n c hcC
  let e : Over.mk π ⟶ U := Over.homMk U.left.isoSpec.inv hπ.symm
  let c₀ := e ≫ u₀
  haveI : IsOpenImmersion e.left := inferInstanceAs (IsOpenImmersion U.left.isoSpec.inv)
  haveI : IsOpenImmersion c₀.left := inferInstanceAs (IsOpenImmersion (e.left ≫ u₀.left))
  refine s2v_i2a_retained_pair_point_exact_support n R Y B b K c₀ huniv hcartier
    D J₀ κ₀ α β hαβ ?_ ?_ ?_ x ?_ η
  · exact s2v_i2a_affine_chart_spectrum_ideal u₀.left K _ hK
  · intro t
    exact s2v_i2a_affine_chart_spectrum_ideal u₀.left (D t) _ (hD t)
  · intro t ht
    have H : (D t).comap u₀.left = ⊤ := Scheme.IdealSheafData.ext_of_isAffine (habsent t ht)
    change (D t).comap (U.left.isoSpec.inv ≫ u₀.left) = ⊤
    rw [Scheme.IdealSheafData.comap_comp, H]
    simp
  · obtain ⟨p, hp⟩ := hx
    refine ⟨U.left.isoSpec.hom p, ?_⟩
    change (U.left.isoSpec.inv ≫ u₀.left) (U.left.isoSpec.hom p) = b.left x.underlying
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact hp

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedLabeledStrictChart
import HodgeLean.Foundations.Program.SchoenTowerI2aSpectrumPointRefinement
import HodgeLean.Foundations.Program.SchoenTowerI2aPairStructureConstants
import HodgeLean.Foundations.Program.SchoenTowerI2aAbsentStrictBranch

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A retained paired step has an actual affine etale chart with exact labeled
branch support at the specified complex point and the specified original-field
point; one of the selected labels is absent on this chart.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_retained_pair_point_exact_support
    (n : ℕ) (R : Type) [CommRing R] [IsDomain R]
    [Algebra (MvPolynomial (Fin n) ℂ) R] [Algebra.Etale (MvPolynomial (Fin n) ℂ) R]
    (Y B : Over (Spec ↧ℂ))
    [IsIntegral B.left] [IsLocallyNoetherian B.left]
    (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (c₀ : Over.mk (Spec.map (CommRingCat.ofHom
      ((algebraMap (MvPolynomial (Fin n) ℂ) R).comp MvPolynomial.C))) ⟶ Y) [IsOpenImmersion c₀.left]
    (huniv : ∀ (Z : Over (Spec ↧ℂ)) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    {T : Type} [Fintype T] [DecidableEq T]
    (D : T → Y.left.IdealSheafData) (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n)
    (α β : J₀) (hαβ : α ≠ β)
    (hK : (K.comap c₀.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      (Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) R (MvPolynomial.X (κ₀ α)),
        algebraMap (MvPolynomial (Fin n) ℂ) R (MvPolynomial.X (κ₀ β))}).map
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (hD : ∀ t : J₀, ((D t).comap c₀.left).ideal
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      (Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) R (MvPolynomial.X (κ₀ t))}).map
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (habsent : ∀ t, t ∉ J₀ → (D t).comap c₀.left = ⊤)
    (x : ComplexPoint B) (hx : b.left x.underlying ∈ Set.range c₀.left)
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
  let P := MvPolynomial (Fin n) ℂ
  let π := Spec.map (CommRingCat.ofHom ((algebraMap P R).comp MvPolynomial.C))
  have hij : κ₀ α ≠ κ₀ β := fun h => hαβ (κ₀.injective h)
  obtain ⟨i, j, horient, g, c, hg, hxg, hc, hgb, _, _, hsq, hstrict⟩ :=
    s2v_i2a_retained_labeled_strict_chart_at_point (Spec ↧ℂ) ℂ n R π Y B b K c₀
      huniv hcartier (κ₀ α) (κ₀ β) hij hK J₀ (fun t => D t) κ₀ hD x.underlying hx
  letI : IsOpenImmersion g := hg
  obtain ⟨t₀, ht₀, hslot⟩ : ∃ t₀ : J₀, (t₀ = α ∨ t₀ = β) ∧ κ₀ t₀ = i := by
    rcases horient with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact ⟨α, Or.inl rfl, hi.symm⟩
    · exact ⟨β, Or.inr rfl, hi.symm⟩
  refine ⟨t₀, ht₀, ?_⟩
  refine s2v_i2a_spectrum_point_exact_support_refinement _ B g x hxg η n c hc
    ?_ (fun t => s2c_strictTransform b.left (D t) K) J₀ κ₀ t₀ ?_ ?_
  · have hstructure : g ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ π := by
      rw [← b.w, ← Category.assoc, hgb, Category.assoc, c₀.w]
      rfl
    rw [hstructure]
    exact s2v_i2a_paired_chart_structure_constants ℂ R _ n i j (algebraMap P R) c
      (algebraMap R _) hsq
  · simpa only [hslot] using hstrict
  · intro t ht
    have H := s2v_i2a_absent_strict_branch_on_open_square b.left g c₀.left
      (Spec.map (CommRingCat.ofHom (algebraMap R _))) hgb (D t) K (habsent t ht)
    rw [H]
    rfl

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.SchoenTowerI2aUnitCentreOpenChart
import HodgeLean.Foundations.Program.SchoenTowerI2aUnitCentreBranchIdeals
import HodgeLean.Foundations.Program.SchoenTowerI2aExactSupportFieldRefinement
import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleReduced
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOpenPoints

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained unit-centre step admits an actual affine etale point chart
with exact branch support and the specified original-field point.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_unit_centre_point_exact_support
    (n : ℕ) (Y B U : Over (Spec ↧ℂ))
    [IsAffine U.left]
    (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (u₀ : U ⟶ Y) [IsOpenImmersion u₀.left]
    (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤)) (hc : c.Etale)
    (hcC : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (huniv : ∀ (Z : Over (Spec ↧ℂ)) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    {T : Type} [Fintype T] [DecidableEq T]
    (D : T → Y.left.IdealSheafData) (J₀ : Finset T) (κ₀ : J₀ ↪ Fin n)
    (hK : K.comap u₀.left = ⊤)
    (hD : ∀ t : J₀, ((D t).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {c (MvPolynomial.X (κ₀ t))})
    (habsent : ∀ t, t ∉ J₀ → ((D t).comap u₀.left).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤)
    (x : ComplexPoint B) (hx : b.left x.underlying ∈ Set.range u₀.left)
    {L : Type} [Field L] (η : Spec (CommRingCat.of L) ⟶ B.left) [IsDominant η] :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (u : V ⟶ B) (q : ComplexPoint V),
      IsOpenImmersion u.left ∧ Point.map u q = x ∧
      ∃ ηV : Spec (CommRingCat.of L) ⟶ V.left, ηV ≫ u.left = η ∧ IsDominant ηV ∧
      ∃ (a : MvPolynomial (Fin n) ℂ →+* Γ(V.left, ⊤))
        (J : Finset T) (κ : J ↪ Fin n) (z : T → Γ(V.left, ⊤)),
        J ⊆ J₀ ∧ a.Etale ∧
        a.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.underlying ∈ (s2c_strictTransform b.left (D t) K).support) ∧
        (∀ t : J, z t = a (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((s2c_strictTransform b.left (D t) K).comap u.left).ideal
          ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {z t}) := by
  classical
  obtain ⟨s, hs, hopen, hrange⟩ := s2v_i2a_unit_centre_open_chart b K huniv u₀ hK
  letI : IsOpenImmersion s.left := hopen
  obtain ⟨p, hp⟩ := s0_open_immersion_lift_complex_point s x (by rw [hrange]; exact hx)
  letI : Algebra (MvPolynomial (Fin n) ℂ) Γ(U.left, ⊤) := c.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(U.left, ⊤) := hc.toAlgebra
  let z₀ (t : T) : Γ(U.left, ⊤) :=
    if ht : t ∈ J₀ then c (MvPolynomial.X (κ₀ ⟨t, ht⟩)) else 1
  have hz₀ (t : J₀) : z₀ t = c (MvPolynomial.X (κ₀ t)) := by simp only [z₀, dif_pos t.property]
  have hab₀ (t : T) (ht : t ∉ J₀) : z₀ t = 1 := by simp only [z₀, dif_neg ht]
  have hideal (t : T) :
      ((s2c_strictTransform b.left (D t) K).comap s.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
        Ideal.span {z₀ t} := by
    apply s2v_i2a_unit_centre_affine_strict_ideal b.left s.left u₀.left
      (congrArg (fun f => f.left) hs) (D t) K hK
    · by_cases ht : t ∈ J₀
      · simpa only [z₀, dif_pos ht] using hD ⟨t, ht⟩
      · rw [hab₀ t ht, Ideal.span_singleton_one, habsent t ht]
    · by_cases ht : t ∈ J₀
      · rw [show z₀ t = c (MvPolynomial.X (κ₀ ⟨t, ht⟩)) from hz₀ ⟨t, ht⟩]
        exact s2v_i2a_etale_coordinate_radical ℂ (Fin n) Γ(U.left, ⊤) (κ₀ ⟨t, ht⟩)
      · rw [hab₀ t ht, Ideal.span_singleton_one]
        exact le_top
  obtain ⟨V, hV, r, q, hr, hq, ηV, hηV, hdom, a, J, κ, z, hJ, _, ha, haC, hsupp, hz, hab, hid⟩ :=
    s2v_i2a_exact_support_refinement_with_original_field U B s η p n c hc hcC
      (fun t => s2c_strictTransform b.left (D t) K) J₀ κ₀ z₀ hideal hz₀ hab₀
  letI : IsOpenImmersion r.left := hr
  refine ⟨V, hV, r ≫ s, q, inferInstanceAs (IsOpenImmersion (r.left ≫ s.left)),
    ?_, ηV, hηV, hdom, a, J, κ, z, hJ, ha, haC, ?_, hz, hab, hid⟩
  · change Point.map s (Point.map r q) = x
    rw [hq, hp]
  · simpa only [hp] using hsupp

end HodgeLean.Foundations.Program

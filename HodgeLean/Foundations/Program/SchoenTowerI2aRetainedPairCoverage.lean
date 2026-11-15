import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedReesOpenImmersion
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierPairReesNeighborhood

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The two actual paired Rees maps cover every point of the retained blowup,
using its Cartier test and universal property over the specified affine base.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_retained_pair_rees_cover
    (Q : Scheme.{0}) (R : Type) [CommRing R]
    (π : Spec (CommRingCat.of R) ⟶ Q) (B : Over Q) [IsIntegral B.left]
    (b : B ⟶ Over.mk π) (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (huniv : ∀ (Z : Over Q) (h : Z ⟶ Over.mk π),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    (x y : R)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {x, y}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (gx : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ B.left)
    (gy : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {y, x}) y)) ⟶ B.left)
    (hgx : gx ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)))
    (hgy : gy ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _))) :
    ∀ p : B.left, p ∈ Set.range gx ∨ p ∈ Set.range gy := by
  intro p
  obtain ⟨S, hS, hSd, v, hv, hpv, hfree⟩ :=
    s2v_i2a_cartier_spectrum_neighborhood B.left (K.comap b.left) p (hcartier p)
  letI : CommRing S := hS
  letI : IsDomain S := hSd
  letI : IsOpenImmersion v := hv
  obtain ⟨u, hu⟩ := Spec.map_surjective (v ≫ b.left)
  have hfreespec : Nonempty (((K.comap (Spec.map u)).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of S), ⊤)] Γ(Spec (CommRingCat.of S), ⊤)) := by
    rw [hu, Scheme.IdealSheafData.comap_comp]
    exact hfree
  have he := s2v_i2a_spectrum_cartier_reflection R S u.hom (Ideal.span {x, y}) K hK hfreespec
  rw [Ideal.map_span, Set.image_pair] at he
  obtain ⟨e⟩ := he
  have hKv : (K.comap (v ≫ b.left)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {u.hom x, u.hom y}).map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom := by
    rw [← hu, s2e_affine_comap_ideal, hK, Ideal.map_map]
    have hn : (Spec.map u).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp u.hom :=
      congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality u).symm
    rw [hn, ← Ideal.map_map, Ideal.map_span, Set.image_pair]
  obtain ⟨pS, hpS⟩ := hpv
  obtain ⟨s, hs, hsne, H⟩ := s2v_i2a_cartier_pair_rees_neighborhood R S u.hom x y e pS
  let L := Localization.Away s
  let incl : S →+* L := algebraMap S L
  have hpL : pS ∈ Set.range (PrimeSpectrum.comap incl) := by
    rw [PrimeSpectrum.localization_away_comap_range L s]
    exact hs
  obtain ⟨pL, hpL⟩ := hpL
  have hfreeL : Nonempty ((((K.comap (v ≫ b.left)).comap
      (Spec.map (CommRingCat.ofHom incl))).ideal ⟨⊤, isAffineOpen_top _⟩)
        ≃ₗ[Γ(Spec (CommRingCat.of L), ⊤)] Γ(Spec (CommRingCat.of L), ⊤)) :=
    s2v_i2a_spectrum_cartier_transport S L incl (Ideal.span {u.hom x, u.hom y})
      (K.comap (v ≫ b.left)) hKv
      (s2e_free_ideal_localization (S := L) (Submonoid.powers s) _ ⟨e⟩)
  have cover (a d : R)
      (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {a, d}) a)) ⟶ B.left)
      (hg : g ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)))
      (ψ : s2t_reesChart (Ideal.span {a, d}) a →+* L)
      (hψ : ψ.comp (algebraMap R _) = incl.comp u.hom) : p ∈ Set.range g := by
    have hcomp : Spec.map (CommRingCat.ofHom ψ) ≫ g =
        Spec.map (CommRingCat.ofHom incl) ≫ v := by
      apply s2v_i2a_cartier_scheme_lift_unique Q (Over.mk π) B b K huniv
      · rw [Category.assoc, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ,
          CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
        change Spec.map (CommRingCat.ofHom incl) ≫ Spec.map u =
          Spec.map (CommRingCat.ofHom incl) ≫ v ≫ b.left
        rw [hu]
      · intro q
        refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
        rw [Category.assoc, Scheme.IdealSheafData.comap_comp]
        exact hfreeL
    refine ⟨Spec.map (CommRingCat.ofHom ψ) pL, ?_⟩
    have Hp := congrArg (fun f : Spec (CommRingCat.of L) ⟶ B.left => f pL) hcomp
    change g (Spec.map (CommRingCat.ofHom ψ) pL) = v (PrimeSpectrum.comap incl pL) at Hp
    simpa only [hpL, hpS] using Hp
  rcases H with ⟨_, ψ, hψ, _⟩ | ⟨_, ψ, hψ, _⟩
  · exact Or.inl (cover x y gx hgx ψ hψ)
  · exact Or.inr (cover y x gy hgy ψ hψ)

end HodgeLean.Foundations.Program

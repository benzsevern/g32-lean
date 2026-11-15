import HodgeLean.Foundations.Program.SchoenTowerI2aSelectedReesRestriction
import HodgeLean.Foundations.Program.SchoenTowerI2aAffineCartierTransport
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierLiftUniqueness

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A restricted actual Rees map into an affine Cartier chart supplies a
principal neighborhood and a section of the retained blowup comparison there.
The specified restricted source factors through the same neighborhood.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_retained_rees_section_on_cartier_neighborhood
    (Q : Scheme.{0}) (Y B : Over Q) (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (huniv : ∀ (Z : Over Q) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (R S T : Type) [CommRing R] [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    (u : R →+* S) (x y : R)
    (e : (Ideal.span {u x, u y} : Ideal S) ≃ₗ[S] S)
    (c : Spec (CommRingCat.of R) ⟶ Y.left) (v : Spec (CommRingCat.of S) ⟶ B.left)
    (hvb : v ≫ b.left = Spec.map (CommRingCat.ofHom u) ≫ c)
    (hK : (K.comap (v ≫ b.left)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {u x, u y}).map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
    (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ B.left)
    (hg : g ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ c)
    (ρ : s2t_reesChart (Ideal.span {x, y}) x →+* T) (φ : S →+* T)
    (hφ : φ.comp u = ρ.comp (algebraMap R _)) (hx : ρ (algebraMap R _ x) ≠ 0)
    (hfactor : Spec.map (CommRingCat.ofHom φ) ≫ v = Spec.map (CommRingCat.ofHom ρ) ≫ g) :
    let C := s2t_reesChart (Ideal.span {x, y}) x
    ∃ s : S, s ≠ 0 ∧ IsUnit (φ s) ∧
      ∃ η : Localization.Away s →+* T, ∃ ψ : C →+* Localization.Away s,
        η.comp (algebraMap S _) = φ ∧
        ψ.comp (algebraMap R C) = (algebraMap S _).comp u ∧ η.comp ψ = ρ ∧
        Spec.map (CommRingCat.ofHom ψ) ≫ g =
          Spec.map (CommRingCat.ofHom (algebraMap S _)) ≫ v ∧
        Spec.map (CommRingCat.ofHom η) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S _)) ≫ v =
          Spec.map (CommRingCat.ofHom ρ) ≫ g := by
  intro C
  obtain ⟨s, hs, hsu, η, ψ, hη, hψ, hρ⟩ :=
    s2v_i2a_selected_rees_coefficient_restriction R S T u x y e ρ φ hφ hx
  let L := Localization.Away s
  let incl : S →+* L := algebraMap S L
  have hfree : Nonempty ((((K.comap (v ≫ b.left)).comap
      (Spec.map (CommRingCat.ofHom incl))).ideal ⟨⊤, isAffineOpen_top _⟩)
        ≃ₗ[Γ(Spec (CommRingCat.of L), ⊤)] Γ(Spec (CommRingCat.of L), ⊤)) :=
    s2v_i2a_spectrum_cartier_transport S L incl (Ideal.span {u x, u y})
      (K.comap (v ≫ b.left)) hK
      (s2e_free_ideal_localization (S := L) (Submonoid.powers s) _ ⟨e⟩)
  refine ⟨s, hs, hsu, η, ψ, hη, hψ, hρ, ?_, ?_⟩
  · apply s2v_i2a_cartier_scheme_lift_unique Q Y B b K huniv
    · rw [Category.assoc, hg, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_comp, Spec.map_comp]
      simp only [Category.assoc, hvb]
    · intro p
      refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
      rw [Category.assoc, Scheme.IdealSheafData.comap_comp]
      exact hfree
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hη]
    exact hfactor

end HodgeLean.Foundations.Program

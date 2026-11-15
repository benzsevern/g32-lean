import HodgeLean.Foundations.Program.SchoenAffineSchemeQuotientOrbits

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The map of invariant spectra induced by an equivariant scheme morphism. -/
def s2_quotientComparison {X Y : Scheme.{0}} (G : Type) [Group G]
    (ρX : G →* Aut X) (ρY : G →* Aut Y) (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    letI := s2_schemeSectionAction X G ρX
    letI := s2_schemeSectionAction Y G ρY
    Spec (CommRingCat.of (FixedPoints.subring Γ(X, ⊤) G)) ⟶
      Spec (CommRingCat.of (FixedPoints.subring Γ(Y, ⊤) G)) :=
  Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf))

/-- A commuting equivariant scheme square gives a commuting invariant-spectrum square. -/
theorem s2_quotientComparison_square {U V X Y : Scheme.{0}} (G : Type) [Group G]
    (ρU : G →* Aut U) (ρV : G →* Aut V) (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (i : U ⟶ X) (f : X ⟶ Y) (t : U ⟶ V) (j : V ⟶ Y)
    (hi : ∀ g : G, i ≫ (ρX g).asIso.hom = (ρU g).asIso.hom ≫ i)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f)
    (ht : ∀ g : G, t ≫ (ρV g).asIso.hom = (ρU g).asIso.hom ≫ t)
    (hj : ∀ g : G, j ≫ (ρY g).asIso.hom = (ρV g).asIso.hom ≫ j)
    (hcomm : i ≫ f = t ≫ j) :
    s2_quotientComparison G ρU ρX i hi ≫ s2_quotientComparison G ρX ρY f hf =
      s2_quotientComparison G ρU ρV t ht ≫ s2_quotientComparison G ρV ρY j hj := by
  unfold s2_quotientComparison
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  exact congrArg (fun m : U ⟶ Y => m.appTop a.val) hcomm

/-- Identity equivariant morphisms induce identity invariant-spectrum maps. -/
theorem s2_quotientComparison_id (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X)
    (h : ∀ g : G, (𝟙 X) ≫ (ρ g).asIso.hom = (ρ g).asIso.hom ≫ (𝟙 X)) :
    s2_quotientComparison G ρ ρ (𝟙 X) h = 𝟙 _ := by
  unfold s2_quotientComparison
  have he : s2_fixedSectionPullback G ρ ρ (𝟙 X) h = RingHom.id _ := by
    ext a
    rfl
  rw [he]
  exact Spec.map_id _

/-- Invariant-spectrum maps preserve composition of equivariant morphisms. -/
theorem s2_quotientComparison_comp {X Y Z : Scheme.{0}} (G : Type) [Group G]
    (ρX : G →* Aut X) (ρY : G →* Aut Y) (ρZ : G →* Aut Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ a : G, f ≫ (ρY a).asIso.hom = (ρX a).asIso.hom ≫ f)
    (hg : ∀ a : G, g ≫ (ρZ a).asIso.hom = (ρY a).asIso.hom ≫ g)
    (hfg : ∀ a : G, (f ≫ g) ≫ (ρZ a).asIso.hom = (ρX a).asIso.hom ≫ (f ≫ g)) :
    s2_quotientComparison G ρX ρY f hf ≫ s2_quotientComparison G ρY ρZ g hg =
      s2_quotientComparison G ρX ρZ (f ≫ g) hfg := by
  unfold s2_quotientComparison
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  rfl

end HodgeLean.Foundations.Program

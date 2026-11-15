import HodgeLean.Foundations.Program.TorusAlgebraizationB54Continuity
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Charts

noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G]

theorem b54_complexPoint_in_chart {ι : Type} (v : ι → A)
    (hv : ∀ i, v i ∈ G 1)
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range v))
    (p : Spec ↧ℂ ⟶ Proj G) :
    ∃ (i : ι) (φ : Away G (v i) →+* ℂ),
      Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι G (v i) (hv i) zero_lt_one = p := by
  let U := Proj.affineOpenCoverOfIrrelevantLESpan G v hv (fun _ => zero_lt_one) hcover
  let x := p (IsLocalRing.closedPoint ℂ)
  let i := U.openCover.idx x
  have hRange : Set.range p ⊆ Set.range (Proj.awayι G (v i) (hv i) zero_lt_one) := by
    rintro _ ⟨y, rfl⟩
    obtain rfl := Subsingleton.elim y (IsLocalRing.closedPoint ℂ)
    exact U.openCover.covers x
  let l := IsOpenImmersion.lift (Proj.awayι G (v i) (hv i) zero_lt_one) p hRange
  refine ⟨i, (Spec.preimage l).hom, ?_⟩
  change Spec.map (Spec.preimage l) ≫ _ = p
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ p hRange

theorem b54_chartPoint_scalar (c : ℂ →+* G 0)
    (p : ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))))
    {r : A} (hr : r ∈ G 1) (φ : Away G r →+* ℂ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι G r hr zero_lt_one = p.left)
    (a : ℂ) : φ (fromZeroRingHom G (.powers r) (c a)) = a := by
  have hh := p.w
  dsimp only [Over.mk_hom] at hh
  rw [← hφ, Category.assoc, ← Category.assoc (Proj.awayι G r hr zero_lt_one),
    Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp] at hh
  rw [← Spec.map_id] at hh
  have he : (φ.comp ((fromZeroRingHom G (.powers r)).comp c)) = RingHom.id ℂ := by
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
  exact RingHom.congr_fun he a

end HodgeLean.Foundations.Program

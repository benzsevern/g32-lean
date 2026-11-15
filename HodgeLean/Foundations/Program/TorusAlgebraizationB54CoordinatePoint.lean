import HodgeLean.Foundations.Program.TorusAlgebraizationB54PointCharts
import HodgeLean.Foundations.Program.TorusAlgebraizationB54ChartEvaluation

noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable {A σ ι : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
theorem b54_chartPoint_eq_of_ratios (c : ℂ →+* G 0) (hc : Function.Surjective c)
    (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤)
    (p : ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))))
    (i : ι) (φ : Away G (v i) →+* ℂ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι G (v i) (hv i) zero_lt_one = p.left)
    (q : A →+* ℂ) (hqc : ∀ a, q (c a) = a) (hu : IsUnit (q (v i)))
    (hq : (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) = ⊤)
    (hratios : ∀ j, φ (Away.mk G (hv i) 1 (v j) (by simpa using hv j)) =
      q (v j) / q (v i)) :
    p.left = Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq := by
  have he : φ = b54_awayEvaluation (G := G) q (v i) hu := by
    apply b54_away_ringHom_ext G (hv i) v hv hgen
    · intro a
      obtain ⟨a, rfl⟩ := hc a
      rw [HomogeneousLocalization.algebraMap_eq,
        b54_chartPoint_scalar G c p (hv i) φ hφ, b54_awayEvaluation_fromZero, hqc]
    · intro j
      rw [hratios, b54_awayEvaluation_mk, pow_one, div_eq_mul_inv]
  rw [← hφ, he]
  exact (b54_fromOfGlobalSections_eq_awayEvaluation q (hv i) zero_lt_one hu hq).symm

end HodgeLean.Foundations.Program

import HodgeLean.Foundations.Program.TorusAlgebraizationB54GlobalEvaluation
import HodgeLean.Foundations.Program.TorusAlgebraizationB54CoordinatePoint
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Normalize

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable {A σ ι : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (c : ℂ →+* G 0)

def b54_projChart {r : A} (hr : r ∈ G 1) : Over (Spec ↧ℂ) :=
  Over.mk (Proj.awayι G r hr zero_lt_one ≫
    (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c)))

def b54_projChartMap {r : A} (hr : r ∈ G 1) : b54_projChart G c hr ⟶
    Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c)) :=
  Over.homMk (Proj.awayι G r hr zero_lt_one) rfl

instance {r : A} (hr : r ∈ G 1) : IsOpenImmersion (b54_projChartMap G c hr).left := by
  change IsOpenImmersion (Proj.awayι G r hr zero_lt_one)
  infer_instance

def b54_chartHom {r : A} (hr : r ∈ G 1) (p : ComplexPoint (b54_projChart G c hr)) :
    Away G r →+* ℂ := (Spec.preimage p.left).hom

theorem b54_chartHom_fac {r : A} (hr : r ∈ G 1)
    (p : ComplexPoint (b54_projChart G c hr)) :
    Spec.map (CommRingCat.ofHom (b54_chartHom G c hr p)) ≫ Proj.awayι G r hr zero_lt_one =
      (Point.map (b54_projChartMap G c hr) p).left := by
  change Spec.map (Spec.preimage p.left) ≫ Proj.awayι G r hr zero_lt_one = _
  rw [Spec.map_preimage]
  rfl

def b54_chartCoordinates (v : ι → A) (hv : ∀ i, v i ∈ G 1) (i : ι) :
    ι → Γ((b54_projChart G c (hv i)).left, ⊤) := fun j =>
  (Scheme.ΓSpecIso (.of (Away G (v i)))).inv
    (Away.mk G (hv i) 1 (v j) (by simpa using hv j))

theorem b54_chartCoordinates_value (v : ι → A) (hv : ∀ i, v i ∈ G 1) (i j : ι)
    (p : ComplexPoint (b54_projChart G c (hv i))) :
    b54_globalEvaluation p (b54_chartCoordinates G c v hv i j) =
      b54_chartHom G c (hv i) p (Away.mk G (hv i) 1 (v j) (by simpa using hv j)) := by
  apply b54_globalEvaluation_Spec
  exact (Spec.map_preimage p.left).symm

theorem b54_chartCoordinates_self (v : ι → A) (hv : ∀ i, v i ∈ G 1) (i : ι)
    (p : ComplexPoint (b54_projChart G c (hv i))) :
    b54_globalEvaluation p (b54_chartCoordinates G c v hv i i) = 1 := by
  rw [b54_chartCoordinates_value,
    ← b54_awayNormalize_homogeneous G (hv i) 1 (v i) (hv i),
    b54_awayNormalize_self, map_one]

theorem b54_chartCoordinates_of_evaluation (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (i : ι) (p : ComplexPoint (b54_projChart G c (hv i))) (q : A →+* ℂ)
    (hq : (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) = ⊤)
    (hp : (Point.map (b54_projChartMap G c (hv i)) p).left =
      Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq) :
    q (v i) ≠ 0 ∧ ∀ j, b54_globalEvaluation p (b54_chartCoordinates G c v hv i j) =
      q (v j) / q (v i) := by
  have hf := (b54_chartHom_fac G c (hv i) p).trans hp
  refine ⟨b54_chart_evaluation_denominator G q hq (hv i) _ hf, fun j => ?_⟩
  rw [b54_chartCoordinates_value, b54_chart_evaluation_eq G q hq (hv i) _ hf,
    b54_awayEvaluation_mk, pow_one, div_eq_mul_inv]

theorem b54_chartPoint_of_coordinates [Fintype ι] (hc : Function.Surjective c)
    (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤)
    (i : ι) (p : ComplexPoint (b54_projChart G c (hv i))) (q : A →+* ℂ)
    (hqc : ∀ a, q (c a) = a) (hu : q (v i) ≠ 0)
    (hq : (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) = ⊤)
    (hp : ∀ j, b54_globalEvaluation p (b54_chartCoordinates G c v hv i j) =
      q (v j) / q (v i)) :
    (Point.map (b54_projChartMap G c (hv i)) p).left =
      Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp q) hq := by
  apply b54_chartPoint_eq_of_ratios G c hc v hv hgen _ i
    (b54_chartHom G c (hv i) p) (b54_chartHom_fac G c (hv i) p) q hqc
    (Ne.isUnit hu) hq
  simpa only [b54_chartCoordinates_value] using hp

end HodgeLean.Foundations.Program

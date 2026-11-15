import HodgeLean.Foundations.Program.TorusAlgebraizationB54Naturality
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (c : ℂ →+* G 0)

def b54_awayComplexAlgebra (r : A) : Algebra ℂ (Away G r) :=
  ((fromZeroRingHom G (.powers r)).comp c).toAlgebra

def b54_awayAlgEvaluation (q : A →+* ℂ)
    (hq : ∀ a, q (algebraMap (G 0) A (c a)) = a) (r : A) (hr : IsUnit (q r)) :
    letI := b54_awayComplexAlgebra G c r
    Away G r →ₐ[ℂ] ℂ :=
  letI := b54_awayComplexAlgebra G c r
  { b54_awayEvaluation q r hr with
    commutes' := fun a ↦ (b54_awayEvaluation_fromZero q r hr (c a)).trans (hq a) }

theorem b54_awayAlgEvaluation_continuous {Z : Type*} [TopologicalSpace Z]
    (q : Z → A →+* ℂ) (hq : ∀ z a, q z (algebraMap (G 0) A (c a)) = a)
    (hcont : ∀ a, Continuous (fun z ↦ q z a)) {r : A} {n : ℕ} (hr : r ∈ G n)
    (hunit : ∀ z, IsUnit (q z r)) :
    letI := b54_awayComplexAlgebra G c r
    Continuous (fun z ↦ b54_awayAlgEvaluation G c (q z) (hq z) r (hunit z)) := by
  letI := b54_awayComplexAlgebra G c r
  rw [continuous_induced_rng]
  apply continuous_pi
  intro x
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective G hr x
  change Continuous (fun z ↦ b54_awayEvaluation (q z) r (hunit z) (Away.mk G hr k a ha))
  simp_rw [b54_awayEvaluation_mk]
  exact (hcont a).mul (((hcont r).inv₀ (fun z ↦ (hunit z).ne_zero)).pow k)

def b54_awayOverInclusion {r : A} {n : ℕ} (hr : r ∈ G n) (hn : 0 < n) :
    letI := b54_awayComplexAlgebra G c r
    Over.mk (ComplexPoint.affineSpecStructureMap (Away G r)) ⟶
      Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c)) := by
  letI := b54_awayComplexAlgebra G c r
  refine Over.homMk (Proj.awayι G r hr hn) ?_
  change Proj.awayι G r hr hn ≫ (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c)) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem b54_continuous_proj_chart_evaluation {Z : Type*} [TopologicalSpace Z]
    (q : Z → A →+* ℂ) (hq : ∀ z a, q z (algebraMap (G 0) A (c a)) = a)
    (hcont : ∀ a, Continuous (fun z ↦ q z a)) {r : A} {n : ℕ}
    (hr : r ∈ G n) (hn : 0 < n) (hunit : ∀ z, IsUnit (q z r))
    (p : Z → ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))))
    (hp : ∀ z, (p z).left =
      Spec.map (CommRingCat.ofHom (b54_awayEvaluation (G := G) (q z) r (hunit z))) ≫
        Proj.awayι G r hr hn) : Continuous p := by
  letI := b54_awayComplexAlgebra G c r
  have h := (Point.continuous_map (b54_awayOverInclusion G c hr hn)).comp
    ((ComplexPoint.continuous_affineSpecEquiv_symm (Away G r)).comp
      (b54_awayAlgEvaluation_continuous G c q hq hcont hr hunit))
  apply h.congr
  intro z
  apply Over.OverMorphism.ext
  exact (hp z).symm

theorem b54_continuous_proj_evaluation {Z : Type*} [TopologicalSpace Z]
    (q : Z → A →+* ℂ) (hq : ∀ z a, q z (algebraMap (G 0) A (c a)) = a)
    (hcont : ∀ a, Continuous (fun z ↦ q z a))
    (hcover : ∀ z, ∃ (n : ℕ) (r : A), 0 < n ∧ r ∈ G n ∧ q z r ≠ 0)
    (htop : ∀ z, (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (q z)) = ⊤)
    (p : Z → ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))))
    (hp : ∀ z, (p z).left = Proj.fromOfGlobalSections G
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (q z)) (htop z)) : Continuous p := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨n, r, hn, hr, hz⟩ := hcover z
  let U : Set Z := {w | q w r ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage (hcont r)
  have hlocal : Continuous (fun w : U ↦ p w.val) := by
    apply b54_continuous_proj_chart_evaluation G c
      (fun w : U ↦ q w.val) (fun w ↦ hq w.val)
      (fun a ↦ (hcont a).comp continuous_subtype_val) hr hn
      (fun w ↦ (w.property).isUnit)
    intro w
    rw [hp w.val]
    exact b54_fromOfGlobalSections_eq_awayEvaluation (q w.val) hr hn
      w.property.isUnit (htop w.val)
  exact (continuousOn_iff_continuous_domRestrict.mpr hlocal).continuousAt (hU.mem_nhds hz)

end HodgeLean.Foundations.Program

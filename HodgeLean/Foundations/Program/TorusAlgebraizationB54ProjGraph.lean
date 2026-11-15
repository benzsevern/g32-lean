import HodgeLean.Foundations.Program.TorusAlgebraizationB54ChartCoordinates
import HodgeLean.Foundations.Program.TorusAlgebraizationB54ProductCharts
import HodgeLean.Foundations.Program.TorusAlgebraizationB54OpenCarrier
import HodgeLean.Foundations.Program.TorusAlgebraizationB54RankOne

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open scoped MonoidalCategory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G]

theorem b54_proj_graph_carrier (c : ℂ →+* G 0) (hc : Function.Surjective c)
    {n : ℕ} (v : Fin n → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin (G 0) (Set.range v) = ⊤)
    {T : Type*} (q : T → A →+* ℂ) (hqc : ∀ z a, q z (c a) = a)
    (hq : ∀ z, (HomogeneousIdeal.irrelevant G).toIdeal.map
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (q z)) = ⊤)
    (p : T → ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))))
    (hp : ∀ z, (p z).left = Proj.fromOfGlobalSections G
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (q z)) (hq z))
    (hps : Function.Surjective p) (τ : T → T)
    (f : ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))) →
      ComplexPoint (Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))))
    (hf : ∀ z, f (p z) = p (τ z))
    (m : ℕ) (P : Fin m → MvPolynomial (Fin (n * n)) ℂ)
    (hcone : ∀ w, (∀ k, MvPolynomial.eval w (P k) = 0) ↔
      ∃ (z : T) (t : ℂ), w = t • (fun k => q z (v (finProdFinEquiv.symm k).1) *
        q (τ z) (v (finProdFinEquiv.symm k).2))) :
    ∃ C, IsClosed C ∧
      gagam_graph _ _ f = Point.underlying ⁻¹' C := by
  let X := Over.mk (Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c))
  apply b54_closed_carrier_of_open_chart_equations (gagam_product X X) (gagam_graph X X f)
  intro r
  let r₁ := Point.map (CartesianMonoidalCategory.fst X X) r
  let r₂ := Point.map (CartesianMonoidalCategory.snd X X) r
  have hcover := b54_irrelevant_le_span_generators G v hv hgen
  obtain ⟨i, φ, hφ⟩ := b54_complexPoint_in_chart G v hv hcover r₁.left
  obtain ⟨j, ψ, hψ⟩ := b54_complexPoint_in_chart G v hv hcover r₂.left
  let U := b54_projChart G c (hv i)
  let V := b54_projChart G c (hv j)
  let u := b54_projChartMap G c (hv i)
  let w := b54_projChartMap G c (hv j)
  obtain ⟨r₁', hr₁⟩ := b54_point_lift_openImmersion u r₁ (by
    refine ⟨(Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ), ?_⟩
    exact congrArg (fun g : Spec ↧ℂ ⟶ Proj G => g (IsLocalRing.closedPoint ℂ)) hφ)
  obtain ⟨r₂', hr₂⟩ := b54_point_lift_openImmersion w r₂ (by
    refine ⟨(Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint ℂ), ?_⟩
    exact congrArg (fun g : Spec ↧ℂ ⟶ Proj G => g (IsLocalRing.closedPoint ℂ)) hψ)
  obtain ⟨r', hr'⟩ := b54_product_point_lift u w r r₁' r₂' hr₁ hr₂
  let coords := b54_productCoordinates (b54_chartCoordinates G c v hv i)
    (b54_chartCoordinates G c v hv j)
  let regs : Fin m → Γ((gagam_product U V).left, ⊤) := fun k =>
    MvPolynomial.eval₂Hom (b54_globalScalar (gagam_product U V)) coords (P k)
  refine ⟨gagam_product U V, u ⊗ₘ w, b54_product_map_openImmersion u w, ?_, Set.range regs, ?_⟩
  · exact ⟨r'.underlying, (congrArg Point.underlying hr')⟩
  · intro s
    let s₁ := Point.map (CartesianMonoidalCategory.fst U V) s
    let s₂ := Point.map (CartesianMonoidalCategory.snd U V) s
    let a := fun k => b54_globalEvaluation s₁ (b54_chartCoordinates G c v hv i k)
    let b := fun k => b54_globalEvaluation s₂ (b54_chartCoordinates G c v hv j k)
    let tensor := fun k : Fin (n * n) => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2
    have heval (k : Fin m) : Point.evaluate ⊤ (regs k) s = MvPolynomial.eval tensor (P k) := by
      rw [ComplexPoint.evaluate_top_eq_appTop]
      change b54_globalEvaluation s (regs k) = _
      rw [b54_globalEvaluation_polynomial]
      apply congrArg (fun t => MvPolynomial.eval t (P k))
      funext l
      exact b54_productCoordinates_evaluation _ _ s l
    have hgraph : Point.map (u ⊗ₘ w) s ∈ gagam_graph X X f ↔
        Point.map w s₂ = f (Point.map u s₁) := by
      change (s ≫ (u ⊗ₘ w)) ≫ CartesianMonoidalCategory.snd X X =
        f ((s ≫ (u ⊗ₘ w)) ≫ CartesianMonoidalCategory.fst X X) ↔ _
      dsimp only [X, U, V, s₁, s₂, Point.map]
      simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.tensorHom_fst]
    rw [hgraph]
    simp only [Set.forall_mem_range, heval]
    rw [hcone tensor]
    constructor
    · intro hs
      obtain ⟨z, hz⟩ := hps (Point.map u s₁)
      have hz₁ := (congrArg (fun x => x.left) hz).symm.trans (hp z)
      have hz₂ : (Point.map w s₂).left =
          Proj.fromOfGlobalSections G ((Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (q (τ z))) (hq (τ z)) := by
        rw [hs, ← hz, hf]
        exact hp (τ z)
      obtain ⟨hi, ha⟩ := b54_chartCoordinates_of_evaluation G c v hv i s₁ (q z) (hq z) hz₁
      obtain ⟨hj, hb⟩ := b54_chartCoordinates_of_evaluation G c v hv j s₂ (q (τ z)) (hq (τ z)) hz₂
      refine ⟨z, (q z (v i))⁻¹ * (q (τ z) (v j))⁻¹, ?_⟩
      funext k
      dsimp [tensor, a, b]
      rw [ha, hb]
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    · rintro ⟨z, t, ht⟩
      have hprod (k l : Fin n) : a k * b l = t * (q z (v k) * q (τ z) (v l)) := by
        simpa only [tensor, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
          using congrFun ht (finProdFinEquiv (k, l))
      obtain ⟨hi, hj, ha, hb⟩ := b54_rankOne_normalize a (fun k => q z (v k))
        b (fun k => q (τ z) (v k)) i j
        (b54_chartCoordinates_self G c v hv i s₁)
        (b54_chartCoordinates_self G c v hv j s₂) t hprod
      have hx : Point.map u s₁ = p z := Over.OverMorphism.ext
        ((b54_chartPoint_of_coordinates G c hc v hv hgen i s₁ (q z) (hqc z) hi (hq z) ha).trans (hp z).symm)
      have hy : Point.map w s₂ = p (τ z) := Over.OverMorphism.ext
        ((b54_chartPoint_of_coordinates G c hc v hv hgen j s₂ (q (τ z)) (hqc (τ z)) hj (hq (τ z)) hb).trans (hp (τ z)).symm)
      rw [hx, hy, hf]

end HodgeLean.Foundations.Program

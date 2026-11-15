import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplitDefs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- A surjective map between infinite cyclic integral modules takes a generator
to either sign of any specified target generator. -/
theorem s2v_l1b_action_integer_generator_sign
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (f : A →ₗ[ℤ] B) (hf : Function.Surjective f)
    (a : A) (b : B)
    (ha : Function.Surjective (fun r : ℤ => r • a))
    (hb : Function.Bijective (fun r : ℤ => r • b)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ f a = ε • b := by
  obtain ⟨ε, hε⟩ := hb.2 (f a)
  obtain ⟨v, hv⟩ := hf b
  obtain ⟨r, hr⟩ := ha v
  change ε • b = f a at hε
  change r • a = v at hr
  have hmul : r * ε = 1 := by
    apply hb.1
    change (r * ε) • b = (1 : ℤ) • b
    rw [mul_smul, hε, ← map_zsmul, hr, hv, one_smul]
  exact ⟨ε, Int.isUnit_iff.mp (.of_mul_eq_one r (by rwa [mul_comm])), hε.symm⟩

/-- A homeomorphism induces a bijection on the specified point-complement
relative homology groups. -/
theorem s2v_l1b_action_point_homology_bijective
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (R : Type) [CommRing R] (n : ℕ) :
    Function.Bijective (relativeHomologyMap R n
      (imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x)) := by
  let E : pointComplementPair x ≅ pointComplementPair (e x) :=
    TopPair.isoOfSubset e (fun z => by
      change e z ≠ e x ↔ z ≠ x
      exact e.injective.ne_iff)
  have he : E.hom = imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x := rfl
  rw [← he]
  exact (ConcreteCategory.isIso_iff_bijective ((relativeHomologyFunctor R n).map E.hom)).mp
    inferInstance

/-- Degree transport of a one-dimensional complex chart class retains its
integral generator property. -/
theorem s2v_l1b_action_dimension_one_class_generator
    {M : Type} [TopologicalSpace M] [T1Space M]
    (d : ℕ) [ChartedSpace (Fin d → ℂ) M] (hd : d = 1) (x : M) :
    Function.Bijective (fun r : ℤ => r •
      (show RelativeHomology ℤ (pointComplementPair x) 2 from by
        simpa only [hd, mul_one] using b6m_manifoldLocalClass ℤ d x)) := by
  subst d
  convert b6m_localClassOfChart_one_smul_bijective ℤ (chartAt (Fin 1 → ℂ) x) x
    (mem_chart_source _ x) using 1
  funext r
  exact (Int.cast_smul_eq_zsmul ℤ r _).symm

/-- The specified native local class of the algebraic curve generates its
integral local homology group. -/
theorem s2v_l1b_action_curve_class_generator
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1) (p : ComplexPoint Y) :
    Function.Bijective (fun r : ℤ => r • s2v_l1b_action_curveLocalClass Y hdimY p) :=
  s2v_l1b_action_dimension_one_class_generator (TopologicalSpace.dim Y.left) hdimY p

/-- A homeomorphism to the algebraic curve has a sign on the specified
integral local classes at every point. -/
theorem s2v_l1b_action_local_sign_exists
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M]
    (eY : M ≃ₜ ComplexPoint Y) (x : M) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      relativeHomologyMap ℤ 2
        (imagePointPairMap (TopCat.ofHom ⟨eY, eY.continuous⟩) eY.injective x)
        (b6m_surfaceLocalClass ℤ x) =
          ε • s2v_l1b_action_curveLocalClass Y hdimY (eY x) := by
  letI : T2Space M := eY.symm.t2Space
  have ha : Function.Surjective (fun r : ℤ => r • b6m_surfaceLocalClass ℤ x) := by
    convert (b6m_surfaceLocalClass_smul_bijective ℤ x).2 using 1
    funext r
    exact (Int.cast_smul_eq_zsmul ℤ r _).symm
  exact s2v_l1b_action_integer_generator_sign _
    (s2v_l1b_action_point_homology_bijective eY x ℤ 2).2
    (b6m_surfaceLocalClass ℤ x) (s2v_l1b_action_curveLocalClass Y hdimY (eY x)) ha
    (s2v_l1b_action_curve_class_generator Y hdimY (eY x))

end HodgeLean.Foundations.Program

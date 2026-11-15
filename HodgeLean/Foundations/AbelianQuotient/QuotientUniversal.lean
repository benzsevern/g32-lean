import HodgeLean.Foundations.AbelianQuotient.AnalyticFactorization
import HodgeLean.Foundations.AbelianQuotient.LinearFactor
import HodgeLean.Foundations.AbelianQuotient.LatticeNaturality
import HodgeLean.Foundations.Program.G32SelectedRealizationMaps

noncomputable section
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- A surjective homomorphism with surjective period map has the algebraic quotient universal property. -/
theorem factor_unique_of_period_surjective {A B : Variety} (S : Subvariety A) (q : Hom A B)
    (hs : Function.Surjective (Point.map q.hom))
    (hk : {a : ComplexPoint A.X | Point.map q.hom a = 1} =
      Set.range (Point.map S.inclusion.hom))
    (ψ : abelianPeriodLattice A.X →+ abelianPeriodLattice B.X)
    (hψs : Function.Surjective ψ)
    (hψ : ∀ x l, abelianPeriod A.X (homPullback q.hom 1 x) l = abelianPeriod B.X x (ψ l))
    (T : Variety) (f : Hom A T)
    (hf : S.inclusion.hom ≫ f.hom = (1 : S.B.X ⟶ T.X)) :
    ∃! g : Hom B T, q.hom ≫ g.hom = f.hom := by
  obtain ⟨Q, hQ⟩ := spec_abelianHom_analyticRepresentation q.hom
  obtain ⟨F, hF⟩ := spec_abelianHom_analyticRepresentation f.hom
  have hQs := abq_analyticRepresentation_surjective A B q.hom hs Q hQ
  have hker := analytic_kernel_of_point_kernel S q f hk hf Q F hQ hF
  obtain ⟨G, hG⟩ := exists_linear_factor Q hQs F hker
  have hGlattice : ∀ l ∈ abelianPeriodLattice B.X, G l ∈ abelianPeriodLattice T.X := by
    intro l hl
    obtain ⟨m, hm⟩ := hψs (⟨l, hl⟩ : abelianPeriodLattice B.X)
    have hQm : Q m = l :=
      (analytic_lattice_map_eq q Q hQ ψ hψ m).trans (congrArg Subtype.val hm)
    rw [← hQm]
    have hGm := LinearMap.congr_fun hG (m : Fin (dim A.X.left) → ℂ)
    change G (Q m) = F m at hGm
    rw [hGm]
    exact homPullback_analyticRepresentation_mem_lattice f.hom F hF m
  obtain ⟨g, hgm, hg⟩ := g32x_exists_hom_of_lattice T.X B.X G hGlattice
  let gH : Hom B T := ⟨g, hgm⟩
  have hqg : q.hom ≫ g = f.hom := by
    apply abq_over_hom_ext_of_point_map
    funext a
    obtain ⟨v, hv⟩ := surjective_complexExponential A.X (dim A.X.left) (Additive.ofMul a)
    calc
      Point.map (q.hom ≫ g) a = Point.map g (Point.map q.hom
          (Additive.toMul (complexExponential A.X (dim A.X.left) v))) := by rw [hv]; rfl
      _ = Additive.toMul (complexExponential T.X (dim T.X.left) (G (Q v))) := by
        rw [← hQ, ← hg]
      _ = Point.map f.hom (Additive.toMul (complexExponential A.X (dim A.X.left) v)) := by
        rw [← LinearMap.comp_apply, hG, hF]
      _ = Point.map f.hom a := by rw [hv]; rfl
  refine ⟨gH, hqg, ?_⟩
  intro g' hg'
  have hhom : g'.hom = gH.hom := by
    apply abq_over_hom_ext_of_point_map
    funext b
    obtain ⟨a, rfl⟩ := hs b
    have heq : q.hom ≫ g'.hom = q.hom ≫ gH.hom := hg'.trans hqg.symm
    exact congrArg (fun k : A.X ⟶ T.X => Point.map k a) heq
  cases g' with
  | mk g' mon =>
    change g' = g at hhom
    cases hhom
    rfl

end HodgeLean.Foundations.AbelianQuotient

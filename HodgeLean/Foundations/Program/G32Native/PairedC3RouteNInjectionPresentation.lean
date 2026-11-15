import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplittingMaps
import HodgeLean.Foundations.Program.G32Native.PairedC3LiftedQuotientPresentation
import HodgeLean.Foundations.Program.G32Native.PairedC3ModificationFibreRelation

/-! # A relation presentation retaining the supplied Route N lift -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual supplied quotient and lift give a relation presentation.
The quotient need not be replaced by the canonical hyperplane arrow. -/
theorem paired_c3_route_n_supplied_lift_presentation
    (k : ℕ) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact)
    (q : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₃)
    (hq : Epi q)
    (s : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂)
    (hs : s ≫ E.g = q) :
    ∃ (u : kernel q ⟶ E.X₁ ⊞ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
      (hu : u ≫ biprod.desc E.f s = 0),
      (ShortComplex.mk u (biprod.desc E.f s) hu).ShortExact ∧
      u ≫ biprod.snd = kernel.ι q := by
  letI := hq
  have hK : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    ⟨ShortComplex.exact_kernel q⟩
  obtain ⟨u, v, huv, hP, hu, hf, hv⟩ := paired_c3_presentation_of_quotient_lift
    E.f E.g (kernel.ι q) q E.zero (kernel.condition q) hE hK s hs
  have hv' : v = biprod.desc E.f s := by
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc, hf, hv]
  subst v
  exact ⟨u, huv, hP, hu⟩

/-- Fixed-rank frames force the relation of the supplied lift to remain
nonzero at each complex point; the original quotient arrow is retained.
Source: Hartshorne, Algebraic Geometry, II.5, right exactness of tensor products. -/
theorem paired_c3_route_n_supplied_lift_relation_nonzero
    (k a b : ℕ) (hrank : a + b = k)
    (p : pairedC3Proj k ⟶ Spec ↧ℂ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a b)
    (hframes : ∀ y : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₂ ≅ SheafOfModules.free (Fin k)))
    (q : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₃)
    (hq : Epi q)
    (s : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂)
    (hs : s ≫ E.g = q) :
    ∃ (u : kernel q ⟶ E.X₁ ⊞ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
      (hu : u ≫ biprod.desc E.f s = 0),
      (ShortComplex.mk u (biprod.desc E.f s) hu).ShortExact ∧
      u ≫ biprod.snd = kernel.ι q ∧
      ∀ x : ComplexPoint (Over.mk p), (Scheme.Modules.pullback x.left).map u ≠ 0 := by
  obtain ⟨u, hu, hP, hi⟩ := paired_c3_route_n_supplied_lift_presentation k E hE q hq s hs
  refine ⟨u, hu, hP, hi, ?_⟩
  exact paired_c3_modification_relation_fibre_nonzero k a b hrank p
    E.X₁ E.X₂ (kernel q) e₁ u (biprod.desc E.f s) hu hP hframes

end HodgeLean.Foundations.Program.G32Native

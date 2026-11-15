import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSummand
import HodgeLean.Foundations.Program.G32Native.PairedC3ModificationFibreRelation
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveEndScalars
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSummandZero
import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeFreeZero
import HodgeLean.Foundations.Program.G32Native.PairedC3SplitBundleLocalSummands

/-! # An invertible negative coefficient in an everywhere nonzero relation -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A relation with locally free cokernel has an invertible negative
coefficient when there are fewer trivial directions than projective coordinates.
Source: Hartshorne, Algebraic Geometry, III.5.1; I.2, common zeros of homogeneous linear forms. -/
theorem paired_c3_route_n_negative_coefficient_aux
    (k a b : ℕ) (hk : 0 < k) (hrank : a + (b + 1) = k)
    (M : (pairedC3Proj k).Modules)
    (r : pairedC3NegativeLine k ⟶ pairedC3SplitBundle k a (b + 1) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
    (v : pairedC3SplitBundle k a (b + 1) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ M)
    (hrv : r ≫ v = 0) (hP : (ShortComplex.mk r v hrv).ShortExact)
    (hframes : ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    ∃ i : Fin (b + 1), IsIso (r ≫ biprod.fst ≫ pairedC3NegativeProjection k a b i) := by
  classical
  by_contra h
  have hz (i : Fin (b + 1)) : r ≫ biprod.fst ≫ pairedC3NegativeProjection k a b i = 0 :=
    (paired_c3_negative_end_zero_or_isIso k hk _).resolve_right (by
      intro hi
      exact h ⟨i, hi⟩)
  obtain ⟨l, hl⟩ := paired_c3_zero_negative_factor k a b (r ≫ biprod.fst) hz
  let w := biprod.lift l (r ≫ biprod.snd)
  have hfac : w ≫ biprod.map (pairedC3TrivialInclusion k a (b + 1)) (𝟙 _) = r := by
    apply biprod.hom_ext
    · simp only [w, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
      exact hl.symm
    · simp only [w, Category.assoc, biprod.map_snd, Category.comp_id, biprod.lift_snd]
  let eFree := pairedC3FreeSuccIso (X := pairedC3Proj k) a
  obtain ⟨x, hx⟩ := paired_c3_negative_to_free_zero_fibre k (a + 1) hk (by omega) (w ≫ eFree.hom)
  let G := Scheme.Modules.pullback x.left
  have hw : G.map w = 0 := by
    apply (cancel_mono (G.map eFree.hom)).mp
    simpa only [← CategoryTheory.Functor.map_comp, zero_comp] using hx
  have hne := paired_c3_modification_relation_fibre_nonzero k a (b + 1) hrank
    (conormalPolynomialModelOver k).hom (pairedC3SplitBundle k a (b + 1)) M
    (pairedC3NegativeLine k) (Iso.refl _) r v hrv hP hframes x
  apply hne
  rw [← hfac, CategoryTheory.Functor.map_comp, hw, zero_comp]

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNInjection
import HodgeLean.Foundations.Program.G32Native.PairedC3GlobalMixedSummands

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- N.3: the quotient by those specific lifted directions retains exactly
b negative twisting summands.
Source: Hartshorne, Algebraic Geometry, III.5.1; the hyperplane sequence
and elimination of a nonzero constant relation coefficient. -/
theorem paired_c3_route_n_quotient_aux
    (k a b : ℕ) (hk : 0 < k) (hrank : a + (b + 1) = k)
    (j : Fin (k + 1)) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact) (hqc : E.X₂.IsQuasicoherent)
    (hframes : ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₂ ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) :
          U.toScheme.Modules)))
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a (b + 1))
    (e₃ : E.X₃ ≅ pairedC3HyperplaneQuotient k j)
    (q : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₃)
    (hq : Epi q)
    (s : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂)
    (hs : s ≫ E.g = q)
    (T : ShortComplex (pairedC3Proj k).Modules) (hT : T.ShortExact)
    (h₁ : T.X₁ = (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
    (h₂ : T.X₂ = E.X₂)
    (hf : T.f = eqToHom h₁ ≫ pairedC3LiftMap k a b E e₁ s ≫ eqToHom h₂.symm) :
    Nonempty (T.X₃ ≅ pairedC3SplitBundle k 0 b) := by
  obtain ⟨u, hu, hP, _⟩ :=
    paired_c3_route_n_supplied_lift_presentation k E hE q hq s hs
  obtain ⟨eK⟩ := paired_c3_route_n_quotient_kernel_aux k j E.X₃ e₃ q hq
  let ea := biprod.mapIso e₁ (Iso.refl (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
  let r := eK.hom ≫ u ≫ ea.hom
  let v := ea.inv ≫ biprod.desc E.f s
  have hrv : r ≫ v = 0 := by
    simp only [r, v, Category.assoc, Iso.hom_inv_id_assoc, hu, comp_zero]
  let ep : ShortComplex.mk u (biprod.desc E.f s) hu ≅ ShortComplex.mk r v hrv :=
    ShortComplex.isoMk eK.symm ea (Iso.refl _)
      (by change eK.inv ≫ (eK.hom ≫ u ≫ ea.hom) = u ≫ ea.hom
          rw [Iso.inv_hom_id_assoc])
      (by change ea.hom ≫ (ea.inv ≫ biprod.desc E.f s) = biprod.desc E.f s ≫ 𝟙 _
          rw [Iso.hom_inv_id_assoc, Category.comp_id])
  have hnew := ShortComplex.shortExact_of_iso ep hP
  obtain ⟨i, hcoeff⟩ := paired_c3_route_n_negative_coefficient_aux
    k a b hk hrank E.X₂ r v hrv hnew hframes
  letI := hcoeff
  obtain ⟨e, he⟩ := paired_c3_negative_relation_elimination k a b E.X₂ r v hrv hnew i
  have hw : biprod.map (pairedC3TrivialInclusion k a (b + 1)) (𝟙 _) ≫ v =
      pairedC3LiftMap k a b E e₁ s := by
    apply biprod.hom_ext' <;>
      simp only [v, ea, biprod.mapIso_inv, Iso.refl_inv, pairedC3LiftMap, Category.assoc,
        biprod.inl_map_assoc, biprod.inr_map_assoc, Category.id_comp,
        biprod.inl_desc, biprod.inr_desc, biprod.inl_desc_assoc, biprod.inr_desc_assoc]
  have he' : pairedC3LiftMap k a b E e₁ s ≫ e.hom =
      biprod.map (pairedC3TrivialInclusion k a b) (𝟙 _) := by
    rw [← hw, Category.assoc]
    exact he
  let eQ := pairedC3GlobalLiftCokernelIso k a b E.X₂
    (pairedC3LiftMap k a b E e₁ s) e he'
  let et : cokernel T.f ≅ cokernel (pairedC3LiftMap k a b E e₁ s) :=
    cokernel.mapIso T.f (pairedC3LiftMap k a b E e₁ s)
      (eqToIso h₁) (eqToIso h₂) (by
        simp only [eqToIso.hom, hf, Category.assoc, eqToHom_trans,
          eqToHom_refl, Category.comp_id])
  exact ⟨(hT.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel T.f)) ≪≫ et ≪≫ eQ⟩

end HodgeLean.Foundations.Program.G32Native

import HodgeLean.Foundations.Program.PrymParabolicIntersectionHomology

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem hga_boundary_of_class_zero {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat.{0} R)) (z : LinearMap.ker S.g.hom)
    (hz : S.moduleCatHomologyClass z = 0) : ∃ w, S.f.hom w = z.1 := by
  have hq : (LinearMap.range S.moduleCatToCycles).mkQ z = 0 := by
    apply S.moduleCatHomologyIso.toLinearEquiv.symm.injective
    exact hz.trans (map_zero _).symm
  obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
  exact ⟨w, congrArg Subtype.val hw⟩

set_option backward.isDefEq.respectTransparency false in
theorem hga_relative_boundary_lift (P : TopPair.{0})
    (z : LinearMap.ker (((relativeChainFunctor ℤ).obj P).sc 2).g.hom)
    (hz : (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass z = 0) :
    ∃ w : ((relativeChainFunctor ℤ).obj P).X 3,
      (((relativeChainFunctor ℤ).obj P).d 3 2).hom w = z.1 := by
  let K := (relativeChainFunctor ℤ).obj P
  obtain ⟨v, hv⟩ := hga_boundary_of_class_zero (K.sc 2) z hz
  let hp := ChainComplex.prev ℕ 2
  refine ⟨(K.XIsoOfEq hp).hom.hom v, ?_⟩
  have hd := congrArg (fun m ↦ m.hom v) (K.XIsoOfEq_hom_comp_d hp 2)
  exact hd.trans hv

set_option backward.isDefEq.respectTransparency false in
theorem hga_chain_boundary_mod_subspace (P : TopPair.{0})
    (c : (SingularChainComplex ℤ P.fst).X 2)
    (hc : (((relativeChainFunctor ℤ).obj P).sc 2).g.hom
      (((relativeChainProjection ℤ P).f 2).hom c) = 0)
    (hz : (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass
      ⟨((relativeChainProjection ℤ P).f 2).hom c, hc⟩ = 0) :
    ∃ (w : (SingularChainComplex ℤ P.fst).X 3)
      (u : (SingularChainComplex ℤ P.snd).X 2),
      c = ((SingularChainComplex ℤ P.fst).d 3 2).hom w +
        (show (SingularChainComplex ℤ P.fst).X 2 from
          (((chainPairFunctor ℤ).obj P).hom.f 2).hom u) := by
  let S := relativeChainShortComplex ℤ P
  have hS := relativeChainShortComplex_shortExact ℤ P
  letI := hS.mono_f
  letI := hS.epi_g
  have h2 := hS.map (HomologicalComplex.eval (ModuleCat ℤ) (.down ℕ) 2)
  have h3 := hS.map (HomologicalComplex.eval (ModuleCat ℤ) (.down ℕ) 3)
  obtain ⟨v, hv⟩ := hga_relative_boundary_lift P _ hz
  obtain ⟨w, hw⟩ := h3.moduleCat_surjective_g v
  have he : ((relativeChainProjection ℤ P).f 2).hom
      (c - ((SingularChainComplex ℤ P.fst).d 3 2).hom w) = 0 := by
    rw [map_sub]
    have hd := congrArg (fun m ↦ m.hom w) ((relativeChainProjection ℤ P).comm 3 2).symm
    change ((relativeChainProjection ℤ P).f 2).hom
      (((SingularChainComplex ℤ P.fst).d 3 2).hom w) =
        (((relativeChainFunctor ℤ).obj P).d 3 2).hom
          (((relativeChainProjection ℤ P).f 3).hom w) at hd
    rw [hd, show ((relativeChainProjection ℤ P).f 3).hom w = v from hw, hv, sub_self]
  obtain ⟨u, hu⟩ := (ShortComplex.moduleCat_exact_iff _).mp h2.exact _ he
  refine ⟨w, u, ?_⟩
  change (((chainPairFunctor ℤ).obj P).hom.f 2).hom u =
    c - ((SingularChainComplex ℤ P.fst).d 3 2).hom w at hu
  exact (sub_eq_iff_eq_add').mp hu.symm

set_option backward.isDefEq.respectTransparency false in
theorem hga_point_boundary_of_relative_class_zero {T : Type} [TopologicalSpace T]
    (y : T) (c : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 2) :
    let P := TopPair.ofSubset (X := TopCat.of T) ({y}ᶜ : Set T)
    ∀ hc : (((relativeChainFunctor ℤ).obj P).sc 2).g.hom
      (((relativeChainProjection ℤ P).f 2).hom c) = 0,
      (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass
        ⟨((relativeChainProjection ℤ P).f 2).hom c, hc⟩ = 0 →
      ∃ (w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 3)
        (u : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of ({y}ᶜ : Set T))) 2),
        c = Simplicial.boundary ℤ 2 w + hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2 u := by
  intro P hc hz
  exact hga_chain_boundary_mod_subspace P c hc hz

#print axioms hga_boundary_of_class_zero
#print axioms hga_relative_boundary_lift
#print axioms hga_chain_boundary_mod_subspace
#print axioms hga_point_boundary_of_relative_class_zero

end HodgeLean.Foundations.Program

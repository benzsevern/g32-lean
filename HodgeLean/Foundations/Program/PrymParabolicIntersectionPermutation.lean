import HodgeLean.Foundations.Program.PrymParabolicIntersectionChartClass

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- A triangle with vertices relabelled by a map of its vertex set.
Source: `StdSimplex.map`. -/
def hga_vertexTriangle {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (f : Fin 3 → Fin 3) :
    C(StdSimplex ℝ (Fin 3), T) :=
  σ.comp ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩

/-- A singular tetrahedron obtained by assigning its vertices to a triangle's vertices.
Source: `StdSimplex.map`, `TopCat.toSSetObjEquiv`. -/
def hga_vertexTetrahedron {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (f : Fin 4 → Fin 3) :
    (TopCat.toSSet.obj (TopCat.of T)) _⦋3⦌ :=
  ((TopCat.of T).toSSetObjEquiv _).symm
    (σ.comp ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩)

theorem hga_vertexTetrahedron_face {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (f : Fin 4 → Fin 3) (k : Fin 4) :
    (TopCat.toSSet.obj (TopCat.of T)).δ k (hga_vertexTetrahedron σ f) =
      b3Rest2_triSimplex (hga_vertexTriangle σ (f ∘ k.succAbove)) := by
  apply ((TopCat.of T).toSSetObjEquiv _).injective
  ext a
  change σ (StdSimplex.map f (StdSimplex.map k.succAbove a)) =
    σ (StdSimplex.map (f ∘ k.succAbove) a)
  rw [StdSimplex.map_comp]

set_option backward.isDefEq.respectTransparency false in
theorem hga_swapTetrahedron_boundary {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) :
    Simplicial.boundary ℤ 2
      (Simplicial.chainOfSimplex ℤ (hga_vertexTetrahedron σ ![0, 1, 0, 2])) =
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (hga_vertexTriangle σ ![1, 0, 2])) -
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (hga_vertexTriangle σ ![0, 0, 2])) +
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) -
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (hga_vertexTriangle σ ![0, 1, 0])) := by
  have h0 : (![0, 1, 0, 2] : Fin 4 → Fin 3) ∘ Fin.succ = ![1, 0, 2] := by
    funext i; fin_cases i <;> rfl
  have h1 : (![0, 1, 0, 2] : Fin 4 → Fin 3) ∘ (1 : Fin 4).succAbove = ![0, 0, 2] := by
    funext i; fin_cases i <;> rfl
  have h2 : (![0, 1, 0, 2] : Fin 4 → Fin 3) ∘ (2 : Fin 4).succAbove = id := by
    funext i; fin_cases i <;> rfl
  have h3 : (![0, 1, 0, 2] : Fin 4 → Fin 3) ∘ (3 : Fin 4).succAbove = ![0, 1, 0] := by
    funext i; fin_cases i <;> rfl
  have hid : hga_vertexTriangle σ id = σ := by
    ext a
    change σ (StdSimplex.map id a) = σ a
    rw [StdSimplex.map_id]
  rw [Simplicial.boundary_chainOfSimplex, Fin.sum_univ_four]
  norm_num [hga_vertexTetrahedron_face, h0, h1, h2, h3, hid, sub_eq_add_neg, one_smul, one_zsmul]

theorem hga_vertexTriangle_avoids {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (f : Fin 3 → Fin 3) (j : Fin 3)
    (hj : j ∉ Set.range f) (hb : 0 < b.weights j) (a : StdSimplex ℝ (Fin 3)) :
    hga_vertexTriangle σ f a ≠ σ b := by
  intro h
  have hw := congrArg (fun s : StdSimplex ℝ (Fin 3) ↦ s.weights j) (hσ h)
  change (a.weights.mapDomain f) j = b.weights j at hw
  rw [Finsupp.mapDomain_of_notMem_range a.weights j hj] at hw
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangleSwap_relative_boundary {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, 0 < b.weights i) :
    ∃ (w : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 3)
      (u : Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of ({σ b}ᶜ : Set T))) 2),
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) +
        Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (hga_vertexTriangle σ ![1, 0, 2])) =
        Simplicial.boundary ℤ 2 w + hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2 u := by
  have hn1 : (1 : Fin 3) ∉ Set.range (![0, 0, 2] : Fin 3 → Fin 3) := by
    rintro ⟨i, hi⟩; fin_cases i <;> norm_num at hi
  have hn2 : (2 : Fin 3) ∉ Set.range (![0, 1, 0] : Fin 3 → Fin 3) := by
    rintro ⟨i, hi⟩; fin_cases i <;> norm_num at hi
  let s1 : C(StdSimplex ℝ (Fin 3), ({σ b}ᶜ : Set T)) :=
    ⟨fun a ↦ ⟨hga_vertexTriangle σ ![0, 0, 2] a,
      hga_vertexTriangle_avoids σ hσ b _ 1 hn1 (hb 1) a⟩,
      (hga_vertexTriangle σ ![0, 0, 2]).continuous.subtype_mk _⟩
  let s2 : C(StdSimplex ℝ (Fin 3), ({σ b}ᶜ : Set T)) :=
    ⟨fun a ↦ ⟨hga_vertexTriangle σ ![0, 1, 0] a,
      hga_vertexTriangle_avoids σ hσ b _ 2 hn2 (hb 2) a⟩,
      (hga_vertexTriangle σ ![0, 1, 0]).continuous.subtype_mk _⟩
  have hm (s : C(StdSimplex ℝ (Fin 3), ({σ b}ᶜ : Set T))) :
      hg8_chainMap ⟨Subtype.val, continuous_subtype_val⟩ 2
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex s)) =
      Simplicial.chainOfSimplex ℤ
        (b3Rest2_triSimplex ((⟨Subtype.val, continuous_subtype_val⟩ : C(({σ b}ᶜ : Set T), T)).comp s)) := by
    change ((SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) (ModuleCat.of ℤ ℤ)).f 2).hom _ = _
    rw [Simplicial.chainOfSimplex_map]
    rfl
  refine ⟨Simplicial.chainOfSimplex ℤ (hga_vertexTetrahedron σ ![0, 1, 0, 2]),
    Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex s1) +
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex s2), ?_⟩
  rw [hga_swapTetrahedron_boundary, map_add, hm, hm]
  change _ = _ + (Simplicial.chainOfSimplex ℤ
    (b3Rest2_triSimplex (hga_vertexTriangle σ ![0, 0, 2])) +
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (hga_vertexTriangle σ ![0, 1, 0])))
  abel

set_option backward.isDefEq.respectTransparency false in
theorem hga_class_zero_of_boundary {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat.{0} R)) (z : LinearMap.ker S.g.hom)
    (w : S.X₁) (hw : S.f.hom w = z.1) : S.moduleCatHomologyClass z = 0 := by
  have hq : (LinearMap.range S.moduleCatToCycles).mkQ z = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨w, ?_⟩
    apply Subtype.ext
    exact hw
  change S.moduleCatHomologyIso.inv.hom ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0
  rw [hq, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem hga_relative_class_zero_of_boundary_mod_subspace (P : TopPair.{0})
    (c : (SingularChainComplex ℤ P.fst).X 2)
    (hc : (((relativeChainFunctor ℤ).obj P).sc 2).g.hom
      (((relativeChainProjection ℤ P).f 2).hom c) = 0)
    (w : (SingularChainComplex ℤ P.fst).X 3) (u : (SingularChainComplex ℤ P.snd).X 2)
    (h : c = ((SingularChainComplex ℤ P.fst).d 3 2).hom w +
      (show (SingularChainComplex ℤ P.fst).X 2 from
        (((chainPairFunctor ℤ).obj P).hom.f 2).hom u)) :
    (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass
      ⟨((relativeChainProjection ℤ P).f 2).hom c, hc⟩ = 0 := by
  let K := (relativeChainFunctor ℤ).obj P
  have hu := congrArg (fun m ↦ (m.f 2).hom u) (subspaceChainMap_relativeChainProjection ℤ P)
  change ((relativeChainProjection ℤ P).f 2).hom
    ((((chainPairFunctor ℤ).obj P).hom.f 2).hom u) = 0 at hu
  have hd := ConcreteCategory.congr_hom ((relativeChainProjection ℤ P).comm 3 2) w
  change (K.d 3 2).hom (((relativeChainProjection ℤ P).f 3).hom w) =
    ((relativeChainProjection ℤ P).f 2).hom
      (((SingularChainComplex ℤ P.fst).d 3 2).hom w) at hd
  have hz : (K.d 3 2).hom (((relativeChainProjection ℤ P).f 3).hom w) =
      ((relativeChainProjection ℤ P).f 2).hom c := by
    rw [h, map_add, hu, add_zero]
    exact hd
  apply hga_class_zero_of_boundary (K.sc 2) _
    ((K.XIsoOfEq (ChainComplex.prev ℕ 2)).inv.hom
      (((relativeChainProjection ℤ P).f 3).hom w))
  have ht := ConcreteCategory.congr_hom
    (K.XIsoOfEq_inv_comp_d (ChainComplex.prev ℕ 2) 2)
    (((relativeChainProjection ℤ P).f 3).hom w)
  exact ht.trans hz

set_option backward.isDefEq.respectTransparency false in
theorem hga_relative_native_class_zero_of_boundary (P : TopPair.{0})
    (c : ((relativeChainFunctor ℤ).obj P).cycles 2)
    (a : (SingularChainComplex ℤ P.fst).X 2)
    (hc : (((relativeChainFunctor ℤ).obj P).iCycles 2).hom c =
      ((relativeChainProjection ℤ P).f 2).hom a)
    (w : (SingularChainComplex ℤ P.fst).X 3) (u : (SingularChainComplex ℤ P.snd).X 2)
    (ha : a = ((SingularChainComplex ℤ P.fst).d 3 2).hom w +
      (show (SingularChainComplex ℤ P.fst).X 2 from
        (((chainPairFunctor ℤ).obj P).hom.f 2).hom u)) :
    (((relativeChainFunctor ℤ).obj P).homologyπ 2).hom c = 0 := by
  let K := (relativeChainFunctor ℤ).obj P
  let z := (K.sc 2).moduleCatCyclesIso.hom.hom c
  have hz : z.1 = (K.iCycles 2).hom c :=
    ConcreteCategory.congr_hom (K.sc 2).moduleCatCyclesIso_hom_i c
  have hcy : (K.sc 2).g.hom (((relativeChainProjection ℤ P).f 2).hom a) = 0 := by
    rw [← hc, ← hz]
    exact z.2
  have he : z = ⟨((relativeChainProjection ℤ P).f 2).hom a, hcy⟩ :=
    Subtype.ext (hz.trans hc)
  have hn := hga_cycleClass_of_native_cycle ℤ K 2 z c hz.symm
  rw [← hn, he]
  exact hga_relative_class_zero_of_boundary_mod_subspace P a hcy w u ha

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangleSwap_relative_classes {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, 0 < b.weights i) :
    let P := pointComplementPair (σ b)
    let K := (relativeChainFunctor ℤ).obj P
    ∀ c d : K.cycles 2,
      (K.iCycles 2).hom c = ((relativeChainProjection ℤ P).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)) →
      (K.iCycles 2).hom d = ((relativeChainProjection ℤ P).f 2).hom
        (Simplicial.chainOfSimplex ℤ
          (b3Rest2_triSimplex (hga_vertexTriangle σ ![1, 0, 2]))) →
      (K.homologyπ 2).hom c + (K.homologyπ 2).hom d = 0 := by
  intro P K c d hc hd
  obtain ⟨w, u, hwu⟩ := hga_triangleSwap_relative_boundary σ hσ b hb
  rw [← map_add]
  apply hga_relative_native_class_zero_of_boundary P (c + d)
    (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) +
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex (hga_vertexTriangle σ ![1, 0, 2])))
    _ w u hwu
  rw [map_add, hc, hd, map_add]

#print axioms hga_vertexTriangle
#print axioms hga_vertexTetrahedron
#print axioms hga_vertexTetrahedron_face

#print axioms hga_swapTetrahedron_boundary

#print axioms hga_vertexTriangle_avoids

#print axioms hga_triangleSwap_relative_boundary

#print axioms hga_class_zero_of_boundary

#print axioms hga_relative_class_zero_of_boundary_mod_subspace

#print axioms hga_relative_native_class_zero_of_boundary

#print axioms hga_triangleSwap_relative_classes

end HodgeLean.Foundations.Program

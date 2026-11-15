import HodgeLean.Foundations.Topology.RationalSheafComparisonHomComplex

/-! Cochain transport and the induced map on cohomology classes.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace HodgeLean.Topology.RationalSheafComparison

universe v

variable {C D : Type*} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
  (a : K' ⟶ (F.mapHomologicalComplex (.up ℤ)).obj K)
  (c : (F.mapHomologicalComplex (.up ℤ)).obj L ⟶ L')

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def functorCochainTransport {n : ℤ} (z : Cochain K L n) : Cochain K' L' n :=
  ((Cochain.ofHom a).comp (z.map F) (zero_add n)).comp (Cochain.ofHom c) (add_zero n)

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem functorCochainTransport_differential {n : ℤ} (z : Cochain K L n) (m : ℤ) :
    δ n m (functorCochainTransport F a c z) = functorCochainTransport F a c (δ n m z) := by
  simp only [functorCochainTransport, δ_comp_ofHom, δ_ofHom_comp, δ_map]

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def functorHomTransport : HomComplex K L ⟶ HomComplex K' L' where
  f n := AddCommGrpCat.ofHom
    { toFun := functorCochainTransport F a c
      map_zero' := by simp [functorCochainTransport]
      map_add' z w := by
        simp only [functorCochainTransport, Cochain.map_add, Cochain.comp_add, Cochain.add_comp] }
  comm' n m _ := by
    ext z
    exact functorCochainTransport_differential F a c z m

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def functorCocycleTransport (n : ℤ) : Cocycle K L n →+ Cocycle K' L' n where
  toFun z := ((functorCocycle F z).precomp a).postcomp c
  map_zero' := by ext; simp [Cocycle.precomp, Cocycle.postcomp, functorCocycle]
  map_add' z w := by
    ext
    simp [Cocycle.precomp, Cocycle.postcomp, functorCocycle, Cochain.comp_add, Cochain.add_comp]

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def functorClassTransport (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K' L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' L' n).comp (functorCocycleTransport F a c n)) (by
      intro z hz
      obtain ⟨m, hm, b, hb⟩ := hz
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, functorCochainTransport F a c b, ?_⟩
      rw [functorCochainTransport_differential, hb]
      rfl)

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem functorClassTransport_mk (n : ℤ) (z : Cocycle K L n) :
    functorClassTransport F a c n (.mk z) = .mk (((functorCocycle F z).precomp a).postcomp c) := rfl

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def functorTransportHomologyData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map (functorHomTransport F a c))
      (leftHomologyData K L n) (leftHomologyData K' L' n) where
  φK := AddCommGrpCat.ofHom (functorCocycleTransport F a c n)
  φH := AddCommGrpCat.ofHom (functorClassTransport F a c n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K' L' n).i).mp
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (functorCocycleTransport F a c n) ≫ (leftHomologyData K' L' n).i =
        (leftHomologyData K L n).i ≫ (functorHomTransport F a c).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map
      (functorHomTransport F a c)).comm₁₂.symm
  commπ := rfl

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem homologyAddEquiv_functorHomTransport (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K' L' n (HomologicalComplex.homologyMap (functorHomTransport F a c) n x) =
      functorClassTransport F a c n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (functorTransportHomologyData F a c n).homologyMap_comm x

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem fromSingleEquiv_functorTransport {A : C} {A' : D} (a' : A' ⟶ F.obj A)
    {n : ℤ} (g : A ⟶ L.X n) :
    Cochain.fromSingleEquiv (zero_add n)
      (functorCochainTransport F
        ((CochainComplex.singleFunctor D 0).map a' ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app A) c
        (Cochain.fromSingleMk g (zero_add n))) = a' ≫ F.map g ≫ c.f n := by
  simp [Cochain.fromSingleEquiv, functorCochainTransport, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self, Functor.map_comp]

end HodgeLean.Topology.RationalSheafComparison

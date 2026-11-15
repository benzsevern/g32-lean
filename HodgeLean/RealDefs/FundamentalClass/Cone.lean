import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality
import HodgeLean.RealDefs.FundamentalClass.Bridge

/-! # `[X] = 1`: the cone comparison, generic steps

Each step of upstream's singular-section comparison is a homology map or a cone construction. A
degree-`n` class is carried as `K.liftCycles f ≫ K.homologyπ n` for a morphism `f : A ⟶ K.X n`,
which works in every abelian category (`ModuleCat ℚ` on the relative side, `AddCommGrpCat` on the
sheaf side). The key step is `liftCycles_homologyπ_shortExactHomologyIsoCone`: the short-exact cone
comparison sends the class of `f` to the class of `f ≫ S.f ≫ inl`, with no sign. -/

open CategoryTheory Limits

namespace HodgeLean.RealDefs

section Generic

variable {C : Type*} [Category* C] [Abelian C]

/-- A homology map sends the class of a cycle `f` to the class of `f ≫ φ`. -/
@[reassoc]
lemma liftCycles_homologyπ_homologyMap {K L : CochainComplex C ℤ} (φ : K ⟶ L) {A : C}
    {i j : ℤ} (hj : (ComplexShape.up ℤ).next i = j) (f : A ⟶ K.X i) (hf : f ≫ K.d i j = 0) :
    K.liftCycles f j hj hf ≫ K.homologyπ i ≫ HomologicalComplex.homologyMap φ i =
      L.liftCycles (f ≫ φ.f i) j hj (by rw [Category.assoc, φ.comm, reassoc_of% hf,
        zero_comp]) ≫ L.homologyπ i := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

/-- `mappingCone.map` acts on the `inl` summand through its first component. -/
@[reassoc]
lemma inl_v_mappingCone_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (p q : ℤ) (h : p + (-1) = q) :
    (CochainComplex.mappingCone.inl φ₁).v p q h ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f q =
      a.f p ≫ (CochainComplex.mappingCone.inl φ₂).v p q h := by
  simp [CochainComplex.mappingCone.map]

open CochainComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-`n` component of the shifted fiber lift on the `X₁` summand. -/
lemma shiftedLiftShortComplex_f (S : ShortComplex (CochainComplex C ℤ)) (n n' : ℤ) (h : n' = n + 1) :
    (S.X₁.shiftFunctorObjXIso 1 n n' h).inv ≫
        (mappingCocone.shiftedLiftShortComplex S).f n =
      S.f.f n' ≫ (mappingCone.inl S.g).v n' n (by omega) := by
  subst h
  simp [mappingCocone.shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

open CochainComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The short-exact cone comparison sends the class of a cycle `f` of `X₁` to the class of its
image in the `inl` summand of the cone of `X₂ → X₃`. -/
lemma liftCycles_homologyπ_shortExactHomologyIsoCone (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n n' : ℤ) (h : 1 + n = n') {A : C} (f : A ⟶ S.X₁.X n')
    (j' : ℤ) (hj' : (ComplexShape.up ℤ).next n' = j') (hf : f ≫ S.X₁.d n' j' = 0)
    (j : ℤ) (hj : (ComplexShape.up ℤ).next n = j)
    (hf' : (f ≫ S.f.f n' ≫ (mappingCone.inl S.g).v n' n (by omega)) ≫
      (mappingCone S.g).d n j = 0) :
    S.X₁.liftCycles f j' hj' hf ≫ S.X₁.homologyπ n' ≫
        (mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom =
      (mappingCone S.g).liftCycles (f ≫ S.f.f n' ≫ (mappingCone.inl S.g).v n' n (by omega))
        j hj hf' ≫ (mappingCone S.g).homologyπ n := by
  have hs := liftCycles_shift_homologyπ S.X₁ (n := 1) (i := n)
    (f ≫ (S.X₁.shiftFunctorObjXIso 1 n n' (by omega)).inv) j hj
    (by
      obtain rfl : j = n + 1 := by simpa using hj.symm
      obtain rfl : j' = n' + 1 := by simpa using hj'.symm
      obtain rfl : n' = n + 1 := by omega
      rw [CochainComplex.shiftFunctor_obj_d']
      simp [CochainComplex.shiftFunctorObjXIso, hf]) n' (by omega) j' hj'
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hs
  have hdef : (mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom =
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n n' h).inv.app
        S.X₁ ≫ HomologicalComplex.homologyMap (mappingCocone.shiftedLiftShortComplex S) n := rfl
  rw [hdef, ← reassoc_of% hs, liftCycles_homologyπ_homologyMap]
  congr 1
  simp only [Category.assoc]
  congr 1
  rw [shiftedLiftShortComplex_f S n n' (by omega)]

end Generic


section AbElements

/-- Cycles of a complex of abelian groups are determined by their underlying elements. -/
lemma ab_cycles_ext {K : CochainComplex AddCommGrpCat.{0} ℤ} {i : ℤ} {a b : K.cycles i}
    (h : K.iCycles i a = K.iCycles i b) : a = b :=
  (ConcreteCategory.injective_of_mono_of_preservesPullback (K.iCycles i)) h

/-- A homology map on the class of an element. -/
lemma ab_homologyMap_homologyπ {K L : CochainComplex AddCommGrpCat.{0} ℤ} (φ : K ⟶ L) (i : ℤ)
    (c : K.cycles i) (c' : L.cycles i) (h : L.iCycles i c' = φ.f i (K.iCycles i c)) :
    HomologicalComplex.homologyMap φ i (K.homologyπ i c) = L.homologyπ i c' := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply ab_cycles_ext
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    h]

/-- A cycle is the image of `1` under the lift of the map `1 ↦ its underlying element`. -/
lemma ab_liftCycles_one {K : CochainComplex AddCommGrpCat.{0} ℤ} {i j : ℤ}
    (hj : (ComplexShape.up ℤ).next i = j) (c : K.cycles i) :
    K.liftCycles (AddCommGrpCat.ofHom (zmultiplesHom _ (K.iCycles i c))) j hj (by
      ext
      simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
        Function.comp_apply, zmultiplesHom_apply, map_zsmul, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply]
      rw [← ConcreteCategory.comp_apply, K.iCycles_d, AddCommGrpCat.zero_apply, smul_zero])
      (1 : ℤ) = c := by
  apply ab_cycles_ext
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

open CochainComplex in
/-- The short-exact cone comparison on the class of an element. -/
lemma ab_shortExactHomologyIsoCone_homologyπ (S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ))
    (hS : S.ShortExact) (n n' : ℤ) (h : 1 + n = n') (c : S.X₁.cycles n')
    (c' : (mappingCone S.g).cycles n)
    (hc' : (mappingCone S.g).iCycles n c' =
      (mappingCone.inl S.g).v n' n (by omega) (S.f.f n' (S.X₁.iCycles n' c))) :
    (mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom (S.X₁.homologyπ n' c) =
      (mappingCone S.g).homologyπ n c' := by
  rw [← ab_liftCycles_one (K := S.X₁) (rfl : (ComplexShape.up ℤ).next n' = _) c, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply,
    liftCycles_homologyπ_shortExactHomologyIsoCone S hS n n' h _ _ _ _ _ rfl (by
      ext
      have hd : (mappingCone S.g).d n ((ComplexShape.up ℤ).next n)
          ((mappingCone S.g).iCycles n c') = 0 := by
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]; rfl
      rw [hc'] at hd
      simpa using hd), ConcreteCategory.comp_apply]
  congr 1
  apply ab_cycles_ext
  refine Eq.trans ?_ hc'.symm
  erw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

end AbElements

section ArrowMap

variable {C : Type*} [Category* C] [Abelian C]

open CochainComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone map induced by a map of arrows acts on the `inl` summand through its source
component. -/
@[reassoc]
lemma inl_v_mapArrowHom {K L K' L' : CochainComplex C ℤ} (φ : K ⟶ L) (φ' : K' ⟶ L')
    (H : ∀ j, ∃ i, (ComplexShape.up ℤ).Rel i j) (α : Arrow.mk φ ⟶ Arrow.mk φ') (p q : ℤ)
    (h : p + (-1) = q) :
    (mappingCone.inl φ).v p q h ≫ (HomologicalComplex.homotopyCofiber.mapArrowHom φ φ' H α).f q =
      α.left.f p ≫ (mappingCone.inl φ').v p q h := by
  have hpq : (ComplexShape.up ℤ).Rel q p := by simp; omega
  simp [mappingCone.inl, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ _ _ hpq]

end ArrowMap


section ModElements

/-- Cycles of a complex of `ℚ`-modules are determined by their underlying elements. -/
lemma mod_cycles_ext {K : CochainComplex (ModuleCat.{0} ℚ) ℤ} {i : ℤ} {a b : K.cycles i}
    (h : K.iCycles i a = K.iCycles i b) : a = b :=
  (ConcreteCategory.injective_of_mono_of_preservesPullback (K.iCycles i)) h

/-- A homology map on the class of an element. -/
lemma mod_homologyMap_homologyπ {K L : CochainComplex (ModuleCat.{0} ℚ) ℤ} (φ : K ⟶ L) (i : ℤ)
    (c : K.cycles i) (c' : L.cycles i) (h : L.iCycles i c' = φ.f i (K.iCycles i c)) :
    HomologicalComplex.homologyMap φ i (K.homologyπ i c) = L.homologyπ i c' := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply mod_cycles_ext
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    h]

/-- A cycle is the image of `1` under the lift of the map `1 ↦ its underlying element`. -/
lemma mod_liftCycles_one {K : CochainComplex (ModuleCat.{0} ℚ) ℤ} {i j : ℤ}
    (hj : (ComplexShape.up ℤ).next i = j) (c : K.cycles i) :
    K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ (K.iCycles i c))) j hj (by
      ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero,
        LinearMap.zero_apply]
      rw [← ConcreteCategory.comp_apply, K.iCycles_d]
      simp)
      (1 : ℚ) = c := by
  apply mod_cycles_ext
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

open CochainComplex in
/-- The short-exact cone comparison on the class of an element. -/
lemma mod_shortExactHomologyIsoCone_homologyπ
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℤ))
    (hS : S.ShortExact) (n n' : ℤ) (h : 1 + n = n') (c : S.X₁.cycles n')
    (c' : (mappingCone S.g).cycles n)
    (hc' : (mappingCone S.g).iCycles n c' =
      (mappingCone.inl S.g).v n' n (by omega) (S.f.f n' (S.X₁.iCycles n' c))) :
    (mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom (S.X₁.homologyπ n' c) =
      (mappingCone S.g).homologyπ n c' := by
  rw [← mod_liftCycles_one (K := S.X₁) (rfl : (ComplexShape.up ℤ).next n' = _) c,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    liftCycles_homologyπ_shortExactHomologyIsoCone S hS n n' h _ _ _ _ _ rfl (by
      ext
      have hd : (mappingCone S.g).d n ((ComplexShape.up ℤ).next n)
          ((mappingCone S.g).iCycles n c') = 0 := by
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]; rfl
      rw [hc'] at hd
      simpa using hd), ConcreteCategory.comp_apply]
  congr 1
  apply mod_cycles_ext
  refine Eq.trans ?_ hc'.symm
  erw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

end ModElements


section Functors

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison of an exact functor on classes of cycles. -/
@[reassoc]
lemma homologyπ_mapHomologyIso_hom (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [F.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  have h1 := S.leftHomologyData.homologyπ_comp_homologyIso_hom
  have h0 : S.leftHomologyData.cyclesIso.hom = 𝟙 _ := by
    rw [← cancel_mono S.leftHomologyData.i, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      Category.id_comp]
    rfl
  rw [h0, Category.id_comp] at h1
  have h2 : S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv = S.homologyπ := by
    rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [ShortComplex.LeftHomologyData.map_π, ← F.map_comp, h2]
  rfl

open CochainComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone comparison of an additive functor acts on the `inl` summand by the functor. -/
@[reassoc]
lemma inl_v_mapHomologicalComplexIso_inv {K L : CochainComplex C ℤ} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] (p q : ℤ) (h : p + (-1) = q) :
    (mappingCone.inl ((F.mapHomologicalComplex _).map φ)).v p q h ≫
        (mappingCone.mapHomologicalComplexIso φ F).inv.f q =
      F.map ((mappingCone.inl φ).v p q h) := by
  simp [mappingCone.mapHomologicalComplexIso, mappingCone.mapHomologicalComplexXIso_eq φ F q p
    (by omega)]

end Functors

section Cycles'

variable {C : Type*} [Category* C] [Abelian C]

open CochainComplex in
/-- The `inl` image of a cycle killed by `φ` is a cycle of the cone of `φ`. -/
lemma inl_comp_d_eq_zero {F G : CochainComplex C ℤ} (φ : F ⟶ G) {A : C} (i j k : ℤ)
    (hij : i + (-1) = j) (hik : k + (-1) = i) (y : A ⟶ F.X i) (hy : y ≫ F.d i k = 0)
    (hφ : y ≫ φ.f i = 0) :
    (y ≫ (mappingCone.inl φ).v i j hij) ≫ (mappingCone φ).d j i = 0 := by
  rw [Category.assoc, mappingCone.inl_v_d φ i j k hij hik, Preadditive.comp_sub,
    reassoc_of% hφ, reassoc_of% hy, zero_comp, zero_comp, sub_zero]

end Cycles'

end HodgeLean.RealDefs

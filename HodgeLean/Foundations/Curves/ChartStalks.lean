import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Stalks along affine charts and orders at DVR points

Generic tools for computing `Scheme.ord` on a chart `Spec R ⟶ X`: the stalk at a chart point
is the localization of `R` at the corresponding prime, sections coming from the chart restrict to
the expected elements, and a stalk whose maximal ideal is principal is a DVR at a coheight-one
point. Used for the explicit divisor of `x` on the cubic.
HC no distance; AV milestone no distance.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
noncomputable section
namespace HodgeLean.Foundations.Curves.ChartStalks

variable {X : Scheme}

/-- Sections over an open `U` coming from an affine presentation `U ≅ Spec R`. -/
def chartSection (U : X.Opens) {R : CommRingCat} (e : U.toScheme ≅ Spec R) : R →+* Γ(X, U) :=
  (X.presheaf.map (eqToHom (by simp : U = U.ι ''ᵁ ⊤)).op).hom.comp
    ((U.ι.appIso ⊤).inv.hom.comp (e.hom.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom))

/-- The chart map pulls a chart section back to the corresponding global function on `Spec R`.
Source: Hartshorne, II.2. -/
theorem chartSection_app (U : X.Opens) {R : CommRingCat} (e : U.toScheme ≅ Spec R) (r : R) :
    (e.inv ≫ U.ι).app U (chartSection U e r) =
      (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv r) := by
  set a := (Scheme.ΓSpecIso R).inv r
  have h1 : U.ι.app U (chartSection U e r) = U.toScheme.presheaf.map
      (homOfLE (le_top : U.ι ⁻¹ᵁ U ≤ ⊤)).op (e.hom.appTop a) := by
    simp only [chartSection, Scheme.Opens.ι_app, RingHom.coe_comp, Function.comp_apply,
      Scheme.Opens.ι_appIso, Iso.refl_inv]
    have hF : ∀ {U V W' : X.Opens} (i : V ⟶ U) (j : W' ⟶ V) (x : Γ(X, U)),
        X.presheaf.map j.op (X.presheaf.map i.op x) = X.presheaf.map (j ≫ i).op x := by
      intros; simp
    exact (hF _ _ _).trans rfl
  have h2 : (e.inv ≫ U.ι).app U (chartSection U e r) =
      e.inv.app (U.ι ⁻¹ᵁ U) (U.ι.app U (chartSection U e r)) := rfl
  rw [h2, h1]
  have h3 := ConcreteCategory.congr_hom
    (e.inv.naturality (homOfLE (le_top : U.ι ⁻¹ᵁ U ≤ ⊤)).op) (e.hom.appTop a)
  simp only [CommRingCat.comp_apply] at h3
  refine h3.trans ?_
  have h4 : e.inv.appTop (e.hom.appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
  erw [h4]
  rfl

variable {R : CommRingCat} (g : Spec R ⟶ X) [IsOpenImmersion g]

/-- The stalk of `X` at the image of a point of an open affine chart, as an `R`-algebra. -/
@[instance_reducible]
def chartStalkAlgebra (t : Spec R) : Algebra R (X.presheaf.stalk (g t)) :=
  ((asIso (g.stalkMap t)).commRingCatIsoToRingEquiv.symm.toRingHom.comp
    (StructureSheaf.toStalk R t).hom).toAlgebra

/-- The stalk of `X` at a chart point is the localization of `R` at the corresponding prime.
Source: Hartshorne, II.2.2; Mathlib `StructureSheaf.IsLocalization.to_stalk`. -/
theorem chartStalk_isLocalization (t : Spec R) :
    @IsLocalization.AtPrime R _ (X.presheaf.stalk (g t)) _ (chartStalkAlgebra g t)
      t.asIdeal t.isPrime := by
  have := t.isPrime
  let : Algebra R ((Spec R).presheaf.stalk t) := StructureSheaf.stalkAlgebra R t
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk t) t.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R t
  exact (IsLocalization.isLocalization_iff_of_ringEquiv t.asIdeal.primeCompl
    (asIso (g.stalkMap t)).commRingCatIsoToRingEquiv.symm).mp this

omit [IsOpenImmersion g] in
/-- The stalk map of a chart sends the germ of a chart section to the image of `r`.
Source: Mathlib `Scheme.Hom.germ_stalkMap`. -/
theorem stalkMap_germ_eq_toStalk {U : X.Opens} (s : Γ(X, U)) (r : R)
    (H : g.app U s = (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv r))
    (t : Spec R) (ht : g t ∈ U) :
    g.stalkMap t (X.presheaf.germ U (g t) ht s) = StructureSheaf.toStalk R t r := by
  rw [Scheme.Hom.germ_stalkMap_apply, H]
  rw [(Spec R).presheaf.germ_res_apply (homOfLE le_top) t ht]
  rfl

/-- Germs of chart sections are images of ring elements in the localized stalk.
Source: Hartshorne, II.2.2. -/
theorem germ_eq_chartStalk_algebraMap {U : X.Opens} (s : Γ(X, U)) (r : R)
    (H : g.app U s = (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv r))
    (t : Spec R) (ht : g t ∈ U) :
    X.presheaf.germ U (g t) ht s = @algebraMap R _ _ _ (chartStalkAlgebra g t) r := by
  apply (asIso (g.stalkMap t)).commRingCatIsoToRingEquiv.injective
  change Scheme.Hom.stalkMap g t (X.presheaf.germ U (g t) ht s) =
    Scheme.Hom.stalkMap g t ((asIso (g.stalkMap t)).inv (StructureSheaf.toStalk R t r))
  rw [stalkMap_germ_eq_toStalk g s r H t ht]
  have hinv : ∀ y, Scheme.Hom.stalkMap g t (inv (Scheme.Hom.stalkMap g t) y) = y := fun y ↦ by
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  rw [asIso_inv]
  exact (hinv _).symm

omit [IsOpenImmersion g] in
/-- Composing a chart with `Spec ψ` sends a chart section of `r` to the section of `ψ r`.
Source: Mathlib `Scheme.ΓSpecIso_inv_naturality`. -/
theorem app_comp_specMap {T : CommRingCat} (ψ : R ⟶ T) {U : X.Opens} (s : Γ(X, U)) (r : R)
    (H : g.app U s = (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv r)) :
    (Spec.map ψ ≫ g).app U s =
      (Spec T).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso T).inv (ψ r)) := by
  have h2 : (Spec.map ψ ≫ g).app U s = (Spec.map ψ).app (g ⁻¹ᵁ U) (g.app U s) := rfl
  rw [h2, H]
  have h3 := ConcreteCategory.congr_hom
    ((Spec.map ψ).naturality (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op) ((Scheme.ΓSpecIso R).inv r)
  simp only [CommRingCat.comp_apply] at h3
  refine h3.trans ?_
  have h4 := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality ψ) r
  simp only [CommRingCat.comp_apply] at h4
  erw [← h4]
  rfl

/-- A chart section gives the expected rational function, seen through any chart stalk.
Source: Mathlib `Scheme.algebraMap_germ_eq_germToFunctionField`. -/
theorem germToFunctionField_eq [IsIntegral X] {U : X.Opens} [Nonempty U] (s : Γ(X, U)) (r : R)
    (H : g.app U s = (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv r))
    (t : Spec R) (ht : g t ∈ U) :
    X.germToFunctionField U s = algebraMap (X.presheaf.stalk (g t)) X.functionField
      (@algebraMap R _ _ _ (chartStalkAlgebra g t) r) := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X ht,
    germ_eq_chartStalk_algebraMap g s r H t ht]

/-- A Noetherian local domain obtained by localizing at `m ≤ (a, π)`, with `a ∈ (π)` after
localization and `π ≠ 0`, is a DVR with uniformizer `π`.
Source: Atiyah–Macdonald, Proposition 9.2; Mathlib `IsDiscreteValuationRing.TFAE`. -/
theorem dvr_of_span {A : Type*} [CommRing A] (m : Ideal A) [m.IsPrime] (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.AtPrime S m] [IsDomain S] [IsNoetherianRing S] (π a : A)
    (hm : m ≤ Ideal.span {a, π}) (hπ : π ∈ m)
    (ha : algebraMap A S a ∈ Ideal.span {algebraMap A S π}) (hπ0 : algebraMap A S π ≠ 0) :
    IsDiscreteValuationRing S ∧ Irreducible (algebraMap A S π) := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S m
  have hmax : maximalIdeal S = Ideal.span {algebraMap A S π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m S]
    apply le_antisymm
    · refine (Ideal.map_mono hm).trans ?_
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rcases hb with rfl | rfl
      · exact ha
      · exact Ideal.subset_span rfl
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hπ
  have hnf : ¬ IsField S := by
    intro h
    have h0 := (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)
    rw [hmax, Ideal.span_singleton_eq_bot] at h0
    exact hπ0 h0
  have hdvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 5 1).mp
      (show Submodule.IsPrincipal (maximalIdeal S) from ⟨⟨_, hmax⟩⟩)
  exact ⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax⟩

/-- At a point with DVR stalk, the scheme order is read off from the stalk valuation.
Source: Hartshorne, II.6; Mathlib `Scheme.ord_eq_iff`. -/
theorem ord_eq_of_dvr {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (z : X)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] {f : X.functionField} (hf : f ≠ 0) (n : ℤ)
    (h : Ring.ordFrac (X.presheaf.stalk z) f = WithZero.exp n) : X.ord f z = n := by
  have hz : Order.coheight z = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  rw [Scheme.ord_eq_iff hz hf]
  exact h

end HodgeLean.Foundations.Curves.ChartStalks

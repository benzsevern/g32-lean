import HodgeLean.Adapters.NormalCone
import HodgeLean.Adapters.CycleClassFlatPullbackDefs
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Geometric deformation to the normal cone: objects

Stage A3-B2 objects. The extended Rees algebra of stage A3-B1 is made
functorial in the coefficient ring. A deformation family of a scheme `X`
over a field, along a quasi-coherent ideal sheaf, is a scheme over `X` and
the parameter line whose restriction over each affine open `U` is identified
with `Spec R[t, I/t]`, compatibly with both structure maps; here
`R = Γ(X, U)` and `I` is the ideal sheaf on `U`. These identifications are
data of the structure. Existence of a family is a separate statement of the
frozen spec, not a property of these definitions.

The punctured, unit and zero fibres are actual pullbacks along points and the
punctured line. Specialization of a prime cycle is the fundamental cycle of
the zero fibre of the scheme-theoretic closure of its punctured family; it
extends linearly over a quasi-compact scheme. Fundamental cycles take the finiteness of the
components and of the generic lengths as arguments, so every coefficient is an exact length.
No definition here chooses a witness from an open theorem.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry LaurentPolynomial

universe u

/-! ## Functoriality of the affine deformation algebra -/

/-- The extended Rees algebra is functorial for ring maps carrying the ideal into the ideal:
`Σ aₙ tⁿ ↦ Σ φ(aₙ) tⁿ`.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_deformationMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map φ ≤ J) :
    a3cc3_deformationAlgebra I →+* a3cc3_deformationAlgebra J :=
  ((AddMonoidAlgebra.mapRingHom ℤ φ).comp
    (a3cc3_deformationAlgebra I).val.toRingHom).codRestrict
    (a3cc3_deformationAlgebra J).toSubring fun x => by
      change _ ∈ a3cc3_deformationAlgebra J
      rw [a3cc3_mem_deformationAlgebra_iff]
      intro n
      change ((AddMonoidAlgebra.mapRingHom ℤ φ) (x : LaurentPolynomial R)).coeff n ∈ _
      rw [AddMonoidAlgebra.coeff_mapRingHom]
      have hx := (a3cc3_mem_deformationAlgebra_iff I _).mp x.property n
      refine (Ideal.pow_right_mono h _) ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem φ hx

example {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map φ ≤ J) :
    a3b2_deformationMap φ I J h (a3cc3_parameter I) = a3cc3_parameter J := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapRingHom ℤ φ (T 1 : LaurentPolynomial R) = T 1
  rw [T, AddMonoidAlgebra.mapRingHom_single, map_one]
  rfl

/-- Functoriality is compatible with composition, in particular for double localizations.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
theorem a3b2_deformationMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (h₁ : I.map φ ≤ J) (h₂ : J.map ψ ≤ K) :
    (a3b2_deformationMap ψ J K h₂).comp (a3b2_deformationMap φ I J h₁) =
      a3b2_deformationMap (ψ.comp φ) I K
        (by rw [← Ideal.map_map]; exact (Ideal.map_mono h₁).trans h₂) := by
  ext x : 1
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  ext n
  change ((AddMonoidAlgebra.mapRingHom ℤ ψ) ((AddMonoidAlgebra.mapRingHom ℤ φ)
    (x : LaurentPolynomial R))).coeff n =
      ((AddMonoidAlgebra.mapRingHom ℤ (ψ.comp φ)) (x : LaurentPolynomial R)).coeff n
  simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.comp_apply]

/-! ## The parameter line and its points -/

/-- The affine parameter line over a field.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 87. -/
abbrev a3b2_line (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

example (k : Type u) [Field k] : Scheme.{u} := a3b2_line k

/-- The structure map of the line to the base point.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 87. -/
def a3b2_lineToBase (k : Type u) [Field k] :
    a3b2_line k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

example (k : Type u) [Field k] : a3b2_line k ⟶ Spec (CommRingCat.of k) := a3b2_lineToBase k

/-- The rational point `t = c` of the line.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_point (k : Type u) [Field k] (c : k) : Spec (CommRingCat.of k) ⟶ a3b2_line k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))

example (k : Type u) [Field k] : Spec (CommRingCat.of k) ⟶ a3b2_line k := a3b2_point k 0

/-- The punctured line `Spec k[t, t⁻¹]` and its open immersion into the line.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_punctured (k : Type u) [Field k] :
    Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ a3b2_line k :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

example (k : Type u) [Field k] :
    Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ a3b2_line k := a3b2_punctured k

/-- The structure map of the punctured line to the base point.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_puncturedToBase (k : Type u) [Field k] :
    Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

example (k : Type u) [Field k] :
    Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Spec (CommRingCat.of k) :=
  a3b2_puncturedToBase k

/-- The punctured line lies over the base point compatibly with the line.
Source: Mathlib, `Polynomial.toLaurent_C`. -/
theorem a3b2_punctured_lineToBase (k : Type u) [Field k] :
    a3b2_punctured k ≫ a3b2_lineToBase k = a3b2_puncturedToBase k := by
  rw [a3b2_punctured, a3b2_lineToBase, a3b2_puncturedToBase, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp

/-! ## Affine charts of a family -/

/-- Scalars on the sections over an open, from the structure map to the base point.
Source: Mathlib, `AlgebraicGeometry.Scheme.ΓSpecIso` and `Scheme.Hom.appLE`. -/
def a3b2_fieldMap (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp)).hom

example (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) : k →+* Γ(X, U) := a3b2_fieldMap k X p U

/-- The parameter-line coordinate ring maps to the extended Rees algebra by `t ↦ t`.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88. -/
def a3b2_lineMap (k : Type u) [Field k] {R : Type*} [CommRing R] (φ : k →+* R)
    (J : Ideal R) : Polynomial k →+* a3cc3_deformationAlgebra J :=
  Polynomial.eval₂RingHom ((algebraMap R (a3cc3_deformationAlgebra J)).comp φ)
    (a3cc3_parameter J)

example (k : Type u) [Field k] {R : Type*} [CommRing R] (φ : k →+* R) (J : Ideal R) :
    a3b2_lineMap k φ J Polynomial.X = a3cc3_parameter J := by
  simp [a3b2_lineMap]

/-- A deformation family of `X` along the ideal sheaf `I`: a scheme `M` over `X` and the
parameter line, lying over `X ×ₖ 𝔸¹`, together with an identification of the preimage of every
affine open `U` with `Spec Γ(X, U)[t, I(U)/t]` compatible with both structure maps. The
identifications are part of the data.
Source: Fulton, *Intersection Theory*, second edition, §5.1, pp. 87–88, construction of
`M° = M°_X Y` by its affine pieces `Spec A[t, I/t]`. -/
structure A3b2Deformation (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) where
  /-- The total space. -/
  M : Scheme.{u}
  /-- The projection to the ambient scheme. -/
  toX : M ⟶ X
  /-- The projection to the parameter line. -/
  toLine : M ⟶ a3b2_line k
  /-- Both projections lie over the base point. -/
  w : toX ≫ p = toLine ≫ a3b2_lineToBase k
  /-- The affine charts. -/
  chart : ∀ U : X.affineOpens, (toX ⁻¹ᵁ U.1).toScheme ≅
    Spec (CommRingCat.of (a3cc3_deformationAlgebra (I.ideal U)))
  /-- The charts lie over the affine open. -/
  chart_toX : ∀ U : X.affineOpens, (chart U).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (a3cc3_deformationAlgebra (I.ideal U)))) =
    (toX ∣_ U.1) ≫ U.2.isoSpec.hom
  /-- The charts lie over the parameter line, with `t` the parameter. -/
  chart_toLine : ∀ U : X.affineOpens, (chart U).hom ≫
      Spec.map (CommRingCat.ofHom (a3b2_lineMap k (a3b2_fieldMap k X p U.1) (I.ideal U))) =
    (toX ⁻¹ᵁ U.1).ι ≫ toLine

/-- Satisfiability of the structure fields: over an empty scheme every chart is a map between
empty schemes. This checks only that the fields are consistent; existence for every scheme is a
statement of the frozen spec.
Source: Mathlib, `AlgebraicGeometry.isInitialOfIsEmpty`. -/
example (k : Type u) [Field k] (X : Scheme.{u}) [IsEmpty X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) :
    Nonempty (A3b2Deformation k X p I) := by
  have hD : ∀ U : X.affineOpens,
      IsEmpty (Spec (CommRingCat.of (a3cc3_deformationAlgebra (I.ideal U)))) := by
    intro U
    have h1 : IsEmpty (Spec Γ(X, U.1)) := by
      have : IsEmpty (U.1.toScheme) := ⟨fun y => isEmptyElim (y.1 : X)⟩
      exact ⟨fun y => isEmptyElim (U.2.isoSpec.inv y)⟩
    have h2 : Subsingleton Γ(X, U.1) :=
      PrimeSpectrum.isEmpty_iff_subsingleton.mp h1
    have h3 : Subsingleton (a3cc3_deformationAlgebra (I.ideal U)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := LaurentPolynomial Γ(X, U.1)) _ _)⟩
    exact PrimeSpectrum.isEmpty_iff_subsingleton.mpr h3
  have hO : ∀ U : X.affineOpens, IsEmpty ((𝟙 X) ⁻¹ᵁ U.1).toScheme :=
    fun U => ⟨fun y => isEmptyElim (y.1 : X)⟩
  exact ⟨{
    M := X
    toX := 𝟙 X
    toLine := isInitialOfIsEmpty.to _
    w := isInitialOfIsEmpty.hom_ext _ _
    chart := fun U =>
      haveI := hD U
      haveI := hO U
      isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty
    chart_toX := fun U =>
      haveI := hO U
      isInitialOfIsEmpty.hom_ext _ _
    chart_toLine := fun U =>
      haveI := hO U
      isInitialOfIsEmpty.hom_ext _ _ }⟩

/-! ## Fibres -/

/-- The punctured family, the pullback along the punctured line.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
abbrev a3b2_puncturedFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    Scheme.{u} :=
  pullback D.toLine (a3b2_punctured k)

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    a3b2_puncturedFamily D ⟶ D.M := pullback.fst _ _

/-- The comparison of the punctured family with `X ×ₖ (𝔸¹ ∖ 0)`, from the two projections.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_puncturedComparison {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    a3b2_puncturedFamily D ⟶ pullback p (a3b2_puncturedToBase k) :=
  pullback.lift (pullback.fst _ _ ≫ D.toX) (pullback.snd _ _) (by
    rw [Category.assoc, D.w, ← Category.assoc, pullback.condition, Category.assoc,
      a3b2_punctured_lineToBase])

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    a3b2_puncturedComparison D ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.toX :=
  pullback.lift_fst _ _ _

/-- The fibre over `t = 1` and its projection to `X`.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_unitFibreMap {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    pullback D.toLine (a3b2_point k 1) ⟶ X :=
  pullback.fst _ _ ≫ D.toX

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    a3b2_unitFibreMap D = pullback.fst _ _ ≫ D.toX := rfl

/-- The zero fibre, the pullback along `t = 0`.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
abbrev a3b2_zeroFibre {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    Scheme.{u} :=
  pullback D.toLine (a3b2_point k 0)

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) :
    a3b2_zeroFibre D ⟶ Spec (CommRingCat.of k) := pullback.snd _ _

/-- The part of the zero fibre over an affine open of `X`, mapped into the chart domain.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88. -/
def a3b2_zeroFibreRestrict {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (U : X.affineOpens) :
    ((pullback.fst D.toLine (a3b2_point k 0)) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).toScheme ⟶
      (D.toX ⁻¹ᵁ U.1).toScheme :=
  pullback.fst D.toLine (a3b2_point k 0) ∣_ (D.toX ⁻¹ᵁ U.1)

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) (U : X.affineOpens) :
    a3b2_zeroFibreRestrict D U ≫ (D.toX ⁻¹ᵁ U.1).ι =
      ((pullback.fst D.toLine (a3b2_point k 0)) ⁻¹ᵁ (D.toX ⁻¹ᵁ U.1)).ι ≫ pullback.fst _ _ :=
  morphismRestrict_ι _ _

/-- The quotient of the extended Rees algebra by `t`, followed by the stage A3-B1 equivalence
with the ordinary Rees quotient. It sends `a/t` to the degree-one class of `a`.
Source: Fulton, *Intersection Theory*, second edition, §§4.1 and 5.1, p. 88;
`a3b1_specialFiberAlgEquiv` and theorem `a3b1_specialFiber`. -/
def a3b2_coneQuotient {R : Type*} [CommRing R] (J : Ideal R) :
    a3cc3_deformationAlgebra J →+* a3cc3_normalConeRing J :=
  (a3b1_specialFiberAlgEquiv R J).toRingEquiv.toRingHom.comp (Ideal.Quotient.mk _)

example {R : Type*} [CommRing R] (J : Ideal R) (a : J) :
    a3b2_coneQuotient J (a3b1_fractionGenerator R J a) =
      a3b1_coneMonomial R J 1 ⟨a.val, by simpa only [pow_one] using a.property⟩ := by
  apply a3b1_normalConeToSpecialFiber_injective R J
  rw [a3b1_normalConeToSpecialFiber_monomial_one]
  change (a3b1_specialFiberAlgEquiv R J).symm
    ((a3b1_specialFiberAlgEquiv R J)
      (Ideal.Quotient.mk _ (a3b1_fractionGenerator R J a))) = _
  exact (a3b1_specialFiberAlgEquiv R J).symm_apply_apply _

/-! ## Families of closed subschemes -/

/-- The map of zero fibres induced by a map of families over the parameter line.
Source: Fulton, *Intersection Theory*, second edition, §5.2. -/
def a3b2_zeroFibreMap {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {D : A3b2Deformation k X p I}
    {K : X.IdealSheafData}
    (DV : A3b2Deformation k K.subscheme (K.subschemeι ≫ p) (I.comap K.subschemeι))
    (f : DV.M ⟶ D.M) (hL : f ≫ D.toLine = DV.toLine) :
    a3b2_zeroFibre DV ⟶ a3b2_zeroFibre D :=
  pullback.map DV.toLine (a3b2_point k 0) D.toLine (a3b2_point k 0) f (𝟙 _) (𝟙 _)
    (by rw [hL, Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {D : A3b2Deformation k X p I} {K : X.IdealSheafData}
    (DV : A3b2Deformation k K.subscheme (K.subschemeι ≫ p) (I.comap K.subschemeι))
    (f : DV.M ⟶ D.M) (hL : f ≫ D.toLine = DV.toLine) :
    a3b2_zeroFibreMap DV f hL ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f :=
  pullback.lift_fst _ _ _

/-! ## Fundamental cycles with finite data

The fundamental cycle of a closed subscheme is defined from two finiteness facts, passed as
arguments: the subscheme has finitely many irreducible components, and the local ring at each
generic point has finite length. The sum runs over the finite set of generic points and each
coefficient is the exact natural number length, so no coefficient is truncated. On a Noetherian
scheme both facts hold for every closed subscheme (`a3b2_components_finite_of_isNoetherian`,
`a3b2_length_ne_top_of_isLocallyNoetherian` below); for closed subschemes of a zero fibre they are
statements of the frozen spec. -/

/-- The length of the local ring of a closed subscheme at a generic point, as a natural number,
given that it is finite.
Source: Fulton, *Intersection Theory*, second edition, §1.5, the multiplicity `l_{O_{V,X}}`;
Stacks Project, Tag 02QS. -/
def a3b2_genericLength {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤)
    (y : genericPoints J.subscheme) : ℕ :=
  ENat.lift (Module.length (J.subscheme.presheaf.stalk y.1) (J.subscheme.presheaf.stalk y.1))
    (lt_top_iff_ne_top.2 (hl y.1 y.2))

example {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤)
    (y : genericPoints J.subscheme) :
    (a3b2_genericLength J hl y : ℕ∞) =
      Module.length (J.subscheme.presheaf.stalk y.1) (J.subscheme.presheaf.stalk y.1) :=
  ENat.natCast_lift _ _

/-- The fundamental cycle of a closed subscheme: each irreducible component carries the length
of the local ring of the subscheme at its generic point. Nilpotents are retained. The sum is a
finite sum over the generic points, and the lengths are exact natural numbers.
Source: Fulton, *Intersection Theory*, second edition, §1.5, the cycle `[Z]`;
Stacks Project, Tag 02QS. -/
def a3b2_idealCycle {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hc : (irreducibleComponents J.subscheme).Finite)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤) :
    AlgebraicCycle Y ℚ := by
  classical
  exact ∑ y ∈ (genericPoints.finite hc).toFinset.attach,
    Function.locallyFinsuppWithin.single (J.subschemeι y.1)
      (a3b2_genericLength J hl ⟨y.1, (Set.Finite.mem_toFinset _).1 y.2⟩ : ℚ)

example {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hc : (irreducibleComponents J.subscheme).Finite)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤) :
    AlgebraicCycle Y ℚ := a3b2_idealCycle J hc hl

/-- The coefficient of the fundamental cycle at the image of a generic point is its length.
Source: Fulton, *Intersection Theory*, second edition, §1.5; the closed immersion
`Scheme.IdealSheafData.subschemeι` is injective. -/
theorem a3b2_idealCycle_apply {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hc : (irreducibleComponents J.subscheme).Finite)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤)
    (y : genericPoints J.subscheme) :
    a3b2_idealCycle J hc hl (J.subschemeι y.1) = (a3b2_genericLength J hl y : ℚ) := by
  classical
  rw [a3b2_idealCycle]
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟨y.1, (Set.Finite.mem_toFinset _).2 y.2⟩]
  · simp
  · intro b _ hb
    rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right_iff]
    intro h
    exact (hb (Subtype.ext (J.subschemeι.isEmbedding.injective h).symm)).elim
  · intro h
    exact (h (Finset.mem_attach _ _)).elim

/-- Every generic length is positive: the local ring is nonzero.
Source: Mathlib, `Module.length_pos`. -/
theorem a3b2_genericLength_pos {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤)
    (y : genericPoints J.subscheme) : 0 < a3b2_genericLength J hl y := by
  have h : (0 : ℕ∞) <
      Module.length (J.subscheme.presheaf.stalk y.1) (J.subscheme.presheaf.stalk y.1) :=
    Module.length_pos
  rw [a3b2_genericLength, ← ENat.natCast_lt_natCast, ENat.natCast_lift]
  exact h

/-- A closed subscheme of a Noetherian scheme is Noetherian.
Source: Mathlib, `LocallyOfFiniteType.isLocallyNoetherian` and `quasiCompact_iff_compactSpace`;
Hartshorne, *Algebraic Geometry*, II, Exercise 3.13. -/
instance a3b2_subscheme_isNoetherian {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData) :
    IsNoetherian K.subscheme :=
  haveI : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
  haveI : CompactSpace K.subscheme :=
    (quasiCompact_iff_compactSpace K.subschemeι).1 inferInstance
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- On a Noetherian scheme every closed subscheme has finitely many irreducible components.
Source: Mathlib, `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`;
Hartshorne, *Algebraic Geometry*, I, Proposition 1.5. -/
theorem a3b2_components_finite_of_isNoetherian {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) : (irreducibleComponents J.subscheme).Finite :=
  TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- On a locally Noetherian scheme the local ring of a closed subscheme at a generic point is
Artinian, so it has finite length.
Source: Stacks Project, Tag 02QS and Lemma 10.60.5 (tag 00KH); Mathlib,
`IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`. -/
theorem a3b2_length_ne_top_of_isLocallyNoetherian {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData) : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤ := by
  intro y hy
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have hzero : Order.coheight y = 0 := by
    rw [Order.coheight_eq_zero]
    refine fun z hyz ↦ ?_
    have hzy : z ⤳ y := hyz
    show y ⤳ z
    apply specializes_iff_closure_subset.mpr
    have hz : IsIrreducible (closure ({z} : Set J.subscheme)) := isIrreducible_singleton.closure
    exact hy.2 hz (specializes_iff_closure_subset.mp hzy)
  have : Ring.KrullDimLE 0 (J.subscheme.presheaf.stalk y) :=
    krullDimLE_of_coheight_le hzero.le
  have : IsArtinianRing (J.subscheme.presheaf.stalk y) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact Module.length_ne_top

/-- A cycle on a quasi-compact scheme has finite support: its support is locally finite.
Source: Mathlib, `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain` and
`IsCompact.elim_nhds_subcover`. -/
theorem a3b2_support_finite {X : Scheme.{u}} [CompactSpace X] (c : AlgebraicCycle X ℚ) :
    c.support.Finite := by
  choose t ht hfin using fun z => c.supportLocallyFiniteWithinDomain z (Set.mem_univ z)
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover t (fun z _ => ht z)
  refine (s.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  intro y hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  exact Set.mem_biUnion hz ⟨hyz, hy⟩

/-! ## Specialization of cycles -/

/-- The ideal of the scheme-theoretic closure, in the total space, of the punctured family of
the reduced subvariety `closure {x}`: the kernel of the punctured family restricted to the
scheme-theoretic inverse image of that subvariety.
Source: Fulton, *Intersection Theory*, second edition, §5.2, the closure of `V × (𝔸¹ ∖ 0)` in
`M°`; Mathlib, `AlgebraicGeometry.Scheme.Hom.ker`. -/
def a3b2_closureIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (x : X) : D.M.IdealSheafData :=
  Scheme.Hom.ker
    (((ccm3_primeIdeal X x).comap (pullback.fst D.toLine (a3b2_punctured k) ≫ D.toX)).subschemeι ≫
      pullback.fst D.toLine (a3b2_punctured k))

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) (x : X) : D.M.IdealSheafData :=
  a3b2_closureIdeal D x

/-- The zero fibre of the closed family of `closure {x}`, as an ideal sheaf on the zero fibre:
the scheme-theoretic inverse image of the closure ideal.
Source: Fulton, *Intersection Theory*, second edition, §5.2, the special fibre of the closure of
`V × (𝔸¹ ∖ 0)`. -/
abbrev a3b2_zeroClosureIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (x : X) : (a3b2_zeroFibre D).IdealSheafData :=
  (a3b2_closureIdeal D x).comap (pullback.fst D.toLine (a3b2_point k 0))

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) (x : X) :
    (a3b2_zeroFibre D).IdealSheafData :=
  a3b2_zeroClosureIdeal D x

/-- Specialization of the prime cycle `[closure {x}]`: the fundamental cycle of the zero fibre of
its closed family, given the finiteness of its components and generic lengths.
Source: Fulton, *Intersection Theory*, second edition, §5.2, `σ[V] = [C_{V ∩ X} V]`. -/
def a3b2_specializePrime {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (x : X) (hc : (irreducibleComponents (a3b2_zeroClosureIdeal D x).subscheme).Finite)
    (hl : ∀ y ∈ genericPoints (a3b2_zeroClosureIdeal D x).subscheme,
      Module.length ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y)
        ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y) ≠ ⊤) :
    AlgebraicCycle (a3b2_zeroFibre D) ℚ :=
  a3b2_idealCycle (a3b2_zeroClosureIdeal D x) hc hl

example {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} (D : A3b2Deformation k X p I) (x : X)
    (hc : (irreducibleComponents (a3b2_zeroClosureIdeal D x).subscheme).Finite)
    (hl : ∀ y ∈ genericPoints (a3b2_zeroClosureIdeal D x).subscheme,
      Module.length ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y)
        ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y) ≠ ⊤) :
    AlgebraicCycle (a3b2_zeroFibre D) ℚ :=
  a3b2_specializePrime D x hc hl

/-- Specialization of a rational cycle on a quasi-compact scheme, the linear extension of
`a3b2_specializePrime`: a finite sum over the support of the cycle.
Source: Fulton, *Intersection Theory*, second edition, §5.2, linear extension of `σ`. -/
def a3b2_specialize {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (hc : ∀ x : X, (irreducibleComponents (a3b2_zeroClosureIdeal D x).subscheme).Finite)
    (hl : ∀ x : X, ∀ y ∈ genericPoints (a3b2_zeroClosureIdeal D x).subscheme,
      Module.length ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y)
        ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y) ≠ ⊤)
    (c : AlgebraicCycle X ℚ) : AlgebraicCycle (a3b2_zeroFibre D) ℚ :=
  ∑ x ∈ (a3b2_support_finite c).toFinset,
    (a3b2_specializePrime D x (hc x) (hl x)).mapRange (c x * ·) (mul_zero _)

example {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} (D : A3b2Deformation k X p I)
    (hc : ∀ x : X, (irreducibleComponents (a3b2_zeroClosureIdeal D x).subscheme).Finite)
    (hl : ∀ x : X, ∀ y ∈ genericPoints (a3b2_zeroClosureIdeal D x).subscheme,
      Module.length ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y)
        ((a3b2_zeroClosureIdeal D x).subscheme.presheaf.stalk y) ≠ ⊤) :
    a3b2_specialize D hc hl 0 = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  ext y
  simp

end HodgeLean.Adapters

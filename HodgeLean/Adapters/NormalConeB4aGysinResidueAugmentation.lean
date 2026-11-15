import HodgeLean.Adapters.NormalConeB4aGysinArtinianAugmentation

/-! # Constructed augmentations of parameter fibres at residue-valued points -/

noncomputable section
namespace HodgeLean.Adapters

/-- A point valued in the base residue field descends to an augmentation of
the full parameter quotient, retaining its values on source elements. -/
theorem a3b4a_gysin_exists_parameter_augmentation
    {D A : Type*} [CommRing D] [IsLocalRing D] [CommRing A] [Algebra D A]
    (e : A →ₐ[D] IsLocalRing.ResidueField D) :
    let I := (IsLocalRing.maximalIdeal D).map (algebraMap D A)
    letI : Algebra (IsLocalRing.ResidueField D) (A ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    ∃ ε : (A ⧸ I) →ₐ[IsLocalRing.ResidueField D] IsLocalRing.ResidueField D,
      ∀ a : A, ε (Ideal.Quotient.mk I a) = e a := by
  let I := (IsLocalRing.maximalIdeal D).map (algebraMap D A)
  let k := IsLocalRing.ResidueField D
  letI : Algebra k (A ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hI : I ≤ RingHom.ker e := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro d hd
    change e (algebraMap D A d) = 0
    rw [e.commutes]
    exact (IsLocalRing.residue_eq_zero_iff d).mpr hd
  let g := Ideal.Quotient.liftₐ I e (fun a ha => hI ha)
  let ε : (A ⧸ I) →ₐ[k] k :=
    { g.toRingHom with
      commutes' := fun b => by
        obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective b
        change g (algebraMap D (A ⧸ I) d) = algebraMap D k d
        exact g.commutes d }
  exact ⟨ε, fun a => rfl⟩

/-- A residue-valued affine point extends to its source stalk, with the
original evaluations unchanged. -/
theorem a3b4a_gysin_exists_localized_residue_point
    {D R : Type*} [CommRing D] [IsLocalRing D] [CommRing R] [Algebra D R]
    (e : R →ₐ[D] IsLocalRing.ResidueField D) :
    letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    ∃ eL : Localization.AtPrime (RingHom.ker e) →ₐ[D] IsLocalRing.ResidueField D,
      ∀ r : R, eL (algebraMap R (Localization.AtPrime (RingHom.ker e)) r) = e r := by
  letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  have hu : ∀ y : (RingHom.ker e).primeCompl, IsUnit (e y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    exact y.property
  refine ⟨IsLocalization.liftAlgHom
    (S := Localization.AtPrime (RingHom.ker e)) hu, ?_⟩
  intro r
  simp [IsLocalization.liftAlgHom_apply]

/-- An Artinian local parameter fibre at a residue-valued affine point gives
quasi-finiteness, with the fibre augmentation constructed from that point. -/
theorem a3b4a_gysin_quasiFiniteAt_of_residue_point
    {D R : Type*} [CommRing D] [IsLocalRing D] [CommRing R]
    [Algebra D R] [Algebra.FiniteType D R]
    (e : R →ₐ[D] IsLocalRing.ResidueField D) :
    letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    ∀ [IsArtinianRing (Localization.AtPrime (RingHom.ker e) ⧸
      (IsLocalRing.maximalIdeal D).map
        (algebraMap D (Localization.AtPrime (RingHom.ker e))))],
    Algebra.QuasiFiniteAt D (RingHom.ker e) := by
  letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  intro hArt
  let q := RingHom.ker e
  have hover : q.LiesOver (IsLocalRing.maximalIdeal D) := by
    constructor
    ext d
    change d ∈ IsLocalRing.maximalIdeal D ↔ e (algebraMap D R d) = 0
    rw [e.commutes]
    exact (IsLocalRing.residue_eq_zero_iff d).symm
  obtain ⟨eL, _⟩ := a3b4a_gysin_exists_localized_residue_point e
  obtain ⟨ε, _⟩ := a3b4a_gysin_exists_parameter_augmentation eL
  let I := (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q))
  let A := Localization.AtPrime q ⧸ I
  letI : Algebra (IsLocalRing.ResidueField D) A :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hε : Function.Surjective ε := fun b => ⟨algebraMap _ A b, ε.commutes b⟩
  have : Nontrivial A := hε.nontrivial
  exact a3b4a_gysin_quasiFiniteAt_of_augmented_artinian_fibre q ε

/-- An augmentation of a local algebra identifies its residue field with the
scalar field and retains the original evaluation on every local element. -/
theorem a3b4a_gysin_exists_augmented_residue_equiv
    {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [Algebra k D]
    (v : D →ₐ[k] k) :
    ∃ E : IsLocalRing.ResidueField D ≃ₐ[k] k,
      ∀ d : D, E (IsLocalRing.residue D d) = v d := by
  have hv : Function.Surjective v := fun b => ⟨algebraMap k D b, v.commutes b⟩
  have hker : RingHom.ker v = IsLocalRing.maximalIdeal D :=
    IsLocalRing.ker_eq_maximalIdeal v.toRingHom hv
  let ε : IsLocalRing.ResidueField D →ₐ[k] k :=
    Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal D) v (fun d hd => by
      exact (show d ∈ RingHom.ker v from hker.symm ▸ hd))
  have hε : Function.Surjective ε := by
    intro b
    obtain ⟨d, hd⟩ := hv b
    exact ⟨IsLocalRing.residue D d, hd⟩
  exact ⟨AlgEquiv.ofBijective ε ⟨ε.injective, hε⟩, fun d => rfl⟩

/-- Compatible scalar-valued evaluations give a residue-valued source point
with exactly the original source kernel. -/
theorem a3b4a_gysin_exists_residue_point_of_evaluations
    {k D R : Type*} [Field k] [CommRing D] [IsLocalRing D] [CommRing R]
    [Algebra k D] [Algebra k R] [Algebra D R]
    (v : D →ₐ[k] k) (w : R →ₐ[k] k)
    (h : ∀ d : D, w (algebraMap D R d) = v d) :
    ∃ e : R →ₐ[D] IsLocalRing.ResidueField D, RingHom.ker e = RingHom.ker w := by
  obtain ⟨E, hE⟩ := a3b4a_gysin_exists_augmented_residue_equiv v
  let e : R →ₐ[D] IsLocalRing.ResidueField D :=
    { E.symm.toRingHom.comp w.toRingHom with
      commutes' := fun d => by
        apply E.injective
        change E (E.symm (w (algebraMap D R d))) = E (IsLocalRing.residue D d)
        rw [E.apply_symm_apply, h, hE] }
  refine ⟨e, ?_⟩
  ext r
  change E.symm (w r) = 0 ↔ w r = 0
  exact E.symm.map_eq_zero_iff

/-- An Artinian parameter fibre at compatible scalar-valued points is
quasi-finite, with no separately supplied residue-field map. -/
theorem a3b4a_gysin_quasiFiniteAt_of_evaluations
    {k D R : Type*} [Field k] [CommRing D] [IsLocalRing D] [CommRing R]
    [Algebra k D] [Algebra k R] [Algebra D R] [Algebra.FiniteType D R]
    (v : D →ₐ[k] k) (w : R →ₐ[k] k)
    (h : ∀ d : D, w (algebraMap D R d) = v d)
    (q : Ideal R) [q.IsPrime] (hw : RingHom.ker w = q)
    [IsArtinianRing (Localization.AtPrime q ⧸
      (IsLocalRing.maximalIdeal D).map (algebraMap D (Localization.AtPrime q)))] :
    Algebra.QuasiFiniteAt D q := by
  obtain ⟨e, he⟩ := a3b4a_gysin_exists_residue_point_of_evaluations v w h
  have heq : RingHom.ker e = q := he.trans hw
  clear hw he
  subst q
  exact a3b4a_gysin_quasiFiniteAt_of_residue_point e

end HodgeLean.Adapters

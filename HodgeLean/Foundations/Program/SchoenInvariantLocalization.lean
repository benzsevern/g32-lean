import HodgeLean.Foundations.Program.SchoenInvariantRings
import HodgeLean.Foundations.Program.SchoenLocalizationAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- Invariant numerators can be recovered after localization at invariant denominators. -/
theorem s2_invariants_localization (A B K L G : Type*)
    [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
    [SMulCommClass G A B] [SMulDistribClass G B L]
    [Algebra.IsInvariant A B G]
    (M : Submonoid A) [IsLocalization M K]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) L]
    (hinj : Function.Injective (algebraMap B L)) :
    Algebra.IsInvariant K L G := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B M) x
  obtain ⟨a, ha, has⟩ := s.property
  have hden (g : G) : g • algebraMap B L s = algebraMap B L s := by
    rw [← has, ← algebraMap.smul', smul_algebraMap]
  have hb (g : G) : g • b = b := by
    apply hinj
    rw [algebraMap.smul', ← hs, smul_mul', hx g, hden g]
  obtain ⟨c, hc⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b hb
  refine ⟨IsLocalization.mk' K c ⟨a, ha⟩, ?_⟩
  rw [IsLocalization.algebraMap_mk' B K L]
  apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
  simpa only [hc, has] using hs.symm

/-- The base localization maps to fixed elements of the localized algebra. -/
theorem s2_localized_algebraMap_fixed (A B K L G : Type*)
    [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
    [SMulCommClass G A B] [SMulDistribClass G B L]
    (M : Submonoid A) [IsLocalization M K]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) L]
    (k : K) (g : G) : g • algebraMap K L k = algebraMap K L k := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M k
  have hfixed (a : A) : g • algebraMap A L a = algebraMap A L a := by
    rw [IsScalarTower.algebraMap_apply A B L, ← algebraMap.smul', smul_algebraMap]
  have heq : algebraMap K L k * algebraMap A L s = algebraMap A L a := by
    rw [IsScalarTower.algebraMap_apply A K L, ← map_mul, hs,
      ← IsScalarTower.algebraMap_apply A K L]
  apply (IsLocalization.map_units_map_submonoid B L s).mul_left_inj.mp
  calc
    (g • algebraMap K L k) * algebraMap A L s =
        g • (algebraMap K L k * algebraMap A L s) := by rw [smul_mul', hfixed]
    _ = algebraMap A L a := by rw [heq, hfixed]
    _ = algebraMap K L k * algebraMap A L s := heq.symm

/-- The ring comparison used on invariant affine overlaps. -/
def s2_invariantsLocalizationEquiv (A B K L G : Type*)
    [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
    [SMulCommClass G A B] [SMulDistribClass G B L]
    [Algebra.IsInvariant A B G]
    (M : Submonoid A) [IsLocalization M K]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) L]
    (hAB : Function.Injective (algebraMap A B))
    (hBL : Function.Injective (algebraMap B L)) :
    K ≃+* FixedPoints.subring L G := by
  let f : K →+* FixedPoints.subring L G :=
    (algebraMap K L).codRestrict _ (fun k =>
      s2_localized_algebraMap_fixed A B K L G M k)
  apply RingEquiv.ofBijective f
  constructor
  · intro x y hxy
    have hi : Function.Injective (algebraMap K L) := by
      rw [IsLocalization.algebraMap_eq_map_map_submonoid M B K L]
      letI : IsLocalization (M.map (algebraMap A B)) L :=
        inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B M) L)
      exact IsLocalization.map_injective_of_injective M K L hAB
    exact hi (congrArg Subtype.val hxy)
  · intro x
    have := s2_invariants_localization A B K L G M hBL
    obtain ⟨k, hk⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := G) x.val x.property
    exact ⟨k, Subtype.ext hk⟩

/-- The action on the localization at denominators from the fixed base. -/
@[instance_reducible]
def s2_invariantLocalizationAction (A B G : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (M : Submonoid A) :
    MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid B M)) :=
  s2_localizationAction B _ G (Algebra.algebraMapSubmonoid B M) (by
    intro g b hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [smul_algebraMap]
    exact ⟨a, ha, rfl⟩)

/-- A concrete invariant overlap ring, with the localized action constructed explicitly. -/
def s2_fixedAlgebraLocalizationEquiv (R B G : Type*)
    [CommRing R] [CommRing B] [IsDomain B] [Algebra R B]
    [Group G] [MulSemiringAction G B] [SMulCommClass G R B]
    (M : Submonoid (FixedPoints.subalgebra R B G)) (hM : (0 : FixedPoints.subalgebra R B G) ∉ M) :
    letI := s2_invariantLocalizationAction (FixedPoints.subalgebra R B G) B G M
    Localization M ≃+*
      FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid B M)) G := by
  let A := FixedPoints.subalgebra R B G
  let L := Localization (Algebra.algebraMapSubmonoid B M)
  letI := s2_invariantLocalizationAction A B G M
  letI : Algebra (Localization M) L := localizationAlgebra M B
  have : IsScalarTower A (Localization M) L := isScalarTower_localizationAlgebra M B
  have : SMulDistribClass G B L :=
    s2_localizationAction_smulDistribClass B L G (Algebra.algebraMapSubmonoid B M) _
  apply s2_invariantsLocalizationEquiv A B (Localization M) L G M
    Subtype.val_injective
  apply IsLocalization.injective L (M := Algebra.algebraMapSubmonoid B M)
  rintro b ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro hz
  have ha0 : a = 0 := Subtype.ext hz
  exact hM (ha0 ▸ ha)

end HodgeLean.Foundations.Program

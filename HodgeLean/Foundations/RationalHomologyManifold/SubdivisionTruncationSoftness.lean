import HodgeLean.Foundations.RationalHomologyManifold.BoundaryCokernelSoftness
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionDerivedOrientation
import HodgeLean.Foundations.RationalHomologyManifold.ZeroSheafSoftness

/-! The actual good truncation of the oriented subdivision-limit complex.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual good truncation at the cohomological orientation degree.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; the bounded oriented chain-sheaf model.
HC no distance; AV milestone no distance.
-/
def subdivisionTruncatedSheafComplex (X : TopCat.{0}) (N : ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ :=
  (subdivisionLimitSheafCochainComplex X).truncGE (-(N : ℤ))

#print axioms subdivisionTruncatedSheafComplex
/-- The first term of the actual good truncation is soft in positive orientation degree.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10 and VI.12; the oriented chain truncation cokernel.
HC no distance; AV milestone no distance.
-/
theorem subdivisionTruncatedSheafComplex_first_isSoft (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (n : ℕ)
    (o : LocalRationalOrientation X (n + 1)) :
    IsSoft ((subdivisionTruncatedSheafComplex X (n + 1)).X (-((n + 1 : ℕ) : ℤ))) := by
  let C := subdivisionLimitSheafComplex X
  let K := subdivisionLimitSheafCochainComplex X
  let q := C.d (n + 2) (n + 1)
  let e0 : C.opcycles (n + 1) ≅ cokernel q :=
    (C.opcyclesIsCokernel (n + 2) (n + 1) (ChainComplex.prev ℕ (n + 1))).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let e1 : K.opcycles (-((n + 1 : ℕ) : ℤ)) ≅ C.opcycles (n + 1) :=
    C.extendOpcyclesIso ComplexShape.embeddingDownNat rfl
  let e2 : (subdivisionTruncatedSheafComplex X (n + 1)).X (-((n + 1 : ℕ) : ℤ)) ≅
      K.opcycles (-((n + 1 : ℕ) : ℤ)) := K.truncGEXIsoOpcycles _
  exact isSoft_of_sheaf_iso (e2 ≪≫ e1 ≪≫ e0).symm (subdivision_boundary_cokernel_isSoft X t n o)

#print axioms subdivisionTruncatedSheafComplex_first_isSoft
/-- Every cohomologically regraded subdivision-limit term is soft on a compact Hausdorff space.
Source: Bredon, Sheaf Theory, second edition, VI.12; regrading the soft supported-chain sheaf.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheafCochainTerm_isSoft (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (i : ℤ) :
    IsSoft ((subdivisionLimitSheafCochainComplex X).X i) := by
  let C := subdivisionLimitSheafComplex X
  by_cases hi : 0 < i
  · apply isSoft_of_isZero_sheaf
    change IsZero ((C.extend ComplexShape.embeddingDownNat).X i)
    apply C.isZero_extend_X ComplexShape.embeddingDownNat i
    intro j hj
    change -(j : ℤ) = i at hj
    omega
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = -(m : ℤ) := ⟨(-i).toNat, by omega⟩
    let e : (subdivisionLimitSheafCochainComplex X).X (-(m : ℤ)) ≅ C.X m :=
      C.extendXIso ComplexShape.embeddingDownNat rfl
    exact isSoft_of_sheaf_iso e.symm (subdivisionLimitSheaf_isSoft X m)

#print axioms subdivisionLimitSheafCochainTerm_isSoft
/-- Every term of the actual good truncation is soft in positive orientation dimension.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10 and VI.12; the bounded soft oriented chain model.
HC no distance; AV milestone no distance.
-/
theorem subdivisionTruncatedSheafComplex_isSoft (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1)) (i : ℤ) :
    IsSoft ((subdivisionTruncatedSheafComplex X (n + 1)).X i) := by
  let K := subdivisionLimitSheafCochainComplex X
  let b : ℤ := -((n + 1 : ℕ) : ℤ)
  rcases lt_trichotomy i b with hi | hi | hi
  · apply isSoft_of_isZero_sheaf
    exact (K.truncGE b).isZero_of_isStrictlyGE b i hi
  · subst i
    exact subdivisionTruncatedSheafComplex_first_isSoft X t n o
  · exact isSoft_of_sheaf_iso (K.truncGEXIso b i hi).symm
      (subdivisionLimitSheafCochainTerm_isSoft X i)

#print axioms subdivisionTruncatedSheafComplex_isSoft
/-- The canonical good truncation map retains the actual oriented subdivision-limit derived object.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; truncation at the unique local homology degree.
HC no distance; AV milestone no distance.
-/
theorem subdivisionTruncation_quasiIso (X : TopCat.{0}) [T2Space X] (N : ℕ)
    (o : LocalRationalOrientation X N) :
    QuasiIso ((subdivisionLimitSheafCochainComplex X).πTruncGE (-(N : ℤ))) := by
  let K := subdivisionLimitSheafCochainComplex X
  letI := CochainComplex.isGE_of_homology_concentrated K (-(N : ℤ))
    (subdivisionLimitSheafCochainHomology_concentrated X N o)
  exact inferInstanceAs (QuasiIso (K.πTruncGE (-(N : ℤ))))

#print axioms subdivisionTruncation_quasiIso
/-- Every term of the actual good orientation truncation has vanishing positive sheaf cohomology.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.11 and VI.12; acyclicity of the bounded soft chain model.
HC no distance; AV milestone no distance.
-/
theorem subdivisionTruncatedSheafComplex_positive_cohomology_subsingleton
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (t : FiniteTriangulation X)
    (n : ℕ) (o : LocalRationalOrientation X (n + 1)) (i : ℤ) (k : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((subdivisionTruncatedSheafComplex X (n + 1)).X i) (k + 1)) :=
  spec_subsingleton_cohomology_succ_of_isSoft _ (subdivisionTruncatedSheafComplex_isSoft X t n o i) k

#print axioms subdivisionTruncatedSheafComplex_positive_cohomology_subsingleton
/-- The actual good orientation truncation has zero terms in positive cohomological degrees.
Source: Bredon, Sheaf Theory, second edition, VI.12; the finite cohomological window of the oriented chain model.
HC no distance; AV milestone no distance.
-/
theorem subdivisionTruncatedSheafComplex_isStrictlyLE (X : TopCat.{0}) (N : ℕ) :
    (subdivisionTruncatedSheafComplex X N).IsStrictlyLE 0 := by
  let K := subdivisionLimitSheafCochainComplex X
  letI : K.IsStrictlyLE 0 := by
    dsimp only [K, subdivisionLimitSheafCochainComplex]
    infer_instance
  change (K.truncGE (-(N : ℤ))).IsStrictlyLE 0
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (K.truncGEXIso (-(N : ℤ)) i (by omega)).isZero_iff.mpr
    (K.isZero_of_isStrictlyLE 0 i hi)

#print axioms subdivisionTruncatedSheafComplex_isStrictlyLE
end HodgeLean.Foundations.RationalHomologyManifold

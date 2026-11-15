import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section

open CategoryTheory HodgeLean.Papers

namespace HodgeLean.Foundations.Program

def g32p_complexCharacter (S : g32p_Supplier) : S.H →* ℂˣ :=
  (Circle.toUnits.comp (ZMod.toCircle.toMonoidHom)).comp S.χ

theorem g32p_complexCharacter_apply (S : g32p_Supplier) (h : S.H) :
    (g32p_complexCharacter S h : ℂ) =
      g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val := by
  change (ZMod.toCircle (Multiplicative.toAdd (S.χ h)) : ℂ) = _
  rw [ZMod.toCircle_apply, g32p_root, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem g32p_complexCharacter_unique (S : g32p_Supplier) (χ : S.H →* ℂˣ)
    (hχ : ∀ h, (χ h : ℂ) =
      g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) :
    χ = g32p_complexCharacter S := by
  ext h
  exact (hχ h).trans (g32p_complexCharacter_apply S h).symm

theorem g32p_complexCharacter_ker (S : g32p_Supplier) :
    (g32p_complexCharacter S).ker = S.χ.ker := by
  ext h
  change g32p_complexCharacter S h = 1 ↔ S.χ h = 1
  constructor
  · intro hh
    have hc : ZMod.toCircle (Multiplicative.toAdd (S.χ h)) = ZMod.toCircle (0 : ZMod S.m) := by
      apply Subtype.ext
      have hc := congrArg (fun u : ℂˣ => (u : ℂ)) hh
      change (ZMod.toCircle (Multiplicative.toAdd (S.χ h)) : ℂ) = 1 at hc
      simpa only [AddChar.map_zero_eq_one, Circle.coe_one] using hc
    have hz := ZMod.injective_toCircle hc
    exact congrArg Multiplicative.ofAdd hz
  · intro hh
    change ((Circle.toUnits.comp ZMod.toCircle.toMonoidHom) (S.χ h)) = 1
    rw [hh, map_one]

theorem g32p_root_primitive (S : g32p_Supplier) :
    IsPrimitiveRoot (g32p_root S.m) S.m :=
  Complex.isPrimitiveRoot_exp S.m (NeZero.ne S.m)

def g32p_complexEmbedding (S : g32p_Supplier) :
    HodgeLean.Foundations.cyc_Field S.m →ₐ[ℚ] ℂ :=
  ((IsCyclotomicExtension.zeta_spec S.m ℚ
    (HodgeLean.Foundations.cyc_Field S.m)).embeddingsEquivPrimitiveRoots ℂ
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos S.m))).symm
    ⟨g32p_root S.m, (mem_primitiveRoots (NeZero.pos S.m)).mpr (g32p_root_primitive S)⟩

theorem g32p_complexEmbedding_zeta (S : g32p_Supplier) :
    g32p_complexEmbedding S (g32p_zeta S) = g32p_root S.m := by
  have he := ((IsCyclotomicExtension.zeta_spec S.m ℚ
    (HodgeLean.Foundations.cyc_Field S.m)).embeddingsEquivPrimitiveRoots ℂ
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos S.m))).apply_symm_apply
    ⟨g32p_root S.m, (mem_primitiveRoots (NeZero.pos S.m)).mpr (g32p_root_primitive S)⟩
  have hv := congrArg (fun x : ↥(primitiveRoots S.m ℂ) => (x : ℂ)) he
  simpa only [g32p_complexEmbedding, g32p_zeta,
    IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe] using hv

theorem g32p_complexEmbedding_fieldValue (S : g32p_Supplier) (h : S.H) :
    g32p_complexEmbedding S (g32p_fieldValue S h) = (g32p_complexCharacter S h : ℂ) := by
  rw [g32p_fieldValue, map_pow, g32p_complexEmbedding_zeta,
    g32p_complexCharacter_apply]

end HodgeLean.Foundations.Program

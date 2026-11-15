import HodgeLean.Adapters.NormalConeB4aGysinBridge2FiltrationLength
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Ideal

/-! # Reformulated bridge of A3-B4a: graded pieces of a localization

The graded pieces of the filtration of a localization `T'` of `T` by the powers of an extended
ideal are the localizations of the graded pieces of `T`; free graded pieces stay free of the
same rank. Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Proposition 3.3 and
Corollary 3.4 (exactness of localization). -/

noncomputable section
namespace HodgeLean.Adapters

variable {T T' : Type*} [CommRing T] [CommRing T'] [Algebra T T'] (S : Submonoid T)
  [IsLocalization S T']

/-- Elements of the localizing submonoid act invertibly on modules over the localization. -/
theorem a3b4g_isUnit_algebraMap_end {M : Type*} [AddCommGroup M] [Module T' M] [Module T M]
    [IsScalarTower T T' M] (s : S) : IsUnit (algebraMap T (Module.End T M) s) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units T' s
  rw [Module.End.isUnit_iff]
  constructor
  · intro a b h
    simp only [Module.algebraMap_end_apply] at h
    rw [← algebraMap_smul T' (s : T) a, ← algebraMap_smul T' (s : T) b, ← hu] at h
    simpa [smul_smul] using congrArg (fun m => (↑u⁻¹ : T') • m) h
  · intro b
    refine ⟨(↑u⁻¹ : T') • b, ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [← algebraMap_smul T' (s : T), ← hu, smul_smul, Units.mul_inv, one_smul]

/-- The map of a graded piece `J₁ / J₂` of `T` to the graded piece of the extended ideals. -/
def a3b4g_gradedLocalizationMap (J₁ J₂ : Submodule T T) (J₁' J₂' : Submodule T' T')
    (h₁ : J₁' = Ideal.map (algebraMap T T') J₁) (h₂ : J₂' = Ideal.map (algebraMap T T') J₂) :
    (↥J₁ ⧸ J₂.comap J₁.subtype) →ₗ[T]
      (↥J₁' ⧸ J₂'.comap J₁'.subtype) :=
  Submodule.mapQ _ ((J₂'.comap J₁'.subtype).restrictScalars T)
    { toFun := fun x => ⟨algebraMap T T' x, h₁ ▸ Ideal.mem_map_of_mem _ x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp [Algebra.smul_def] }
    (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem,
        LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
      exact h₂ ▸ Ideal.mem_map_of_mem (algebraMap T T') hx)

theorem a3b4g_gradedLocalizationMap_isLocalizedModule (J₁ J₂ : Submodule T T)
    (J₁' J₂' : Submodule T' T')
    (h₁ : J₁' = Ideal.map (algebraMap T T') J₁) (h₂ : J₂' = Ideal.map (algebraMap T T') J₂) :
    IsLocalizedModule S (a3b4g_gradedLocalizationMap J₁ J₂ J₁' J₂' h₁ h₂) where
  map_units s := a3b4g_isUnit_algebraMap_end (T' := T') S s
  surj y := by
    induction y using Submodule.Quotient.induction_on with
    | _ z =>
      have hz : (z : T') ∈ Ideal.map (algebraMap T T') J₁ := h₁ ▸ z.2
      obtain ⟨⟨x, s⟩, hxs⟩ := (IsLocalization.mem_map_algebraMap_iff S T').mp hz
      refine ⟨⟨Submodule.Quotient.mk x, s⟩, ?_⟩
      change s • Submodule.Quotient.mk z = Submodule.Quotient.mk _
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      ext
      simp only [Submonoid.smul_def, Submodule.coe_smul_of_tower, Algebra.smul_def,
        LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]
      exact hxs
  exists_of_eq {a b} hab := by
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hab
      rw [Submodule.Quotient.eq] at hab
      have hab' : algebraMap T T' ((a : T) - b) ∈ Ideal.map (algebraMap T T') J₂ := by
        rw [← h₂, map_sub]
        exact hab
      obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff S T').mp hab'
      rw [← map_mul] at hys
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S T').mp hys
      refine ⟨c * s, ?_⟩
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
        Submodule.coe_smul, Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul]
      have : ((c : T) * s) * ((a : T) - b) = c * y := by rw [← hc]; ring
      rw [← mul_sub, this]
      exact Ideal.mul_mem_left _ _ y.2

/-- The map `T ⧸ J → T' ⧸ J'` for the extended ideal `J' = J T'`. -/
def a3b4g_quotientLocalizationMap (J : Ideal T) (J' : Ideal T')
    (h : J' = J.map (algebraMap T T')) : (T ⧸ J) →ₗ[T] (T' ⧸ J') :=
  Submodule.mapQ _ ((J' : Submodule T' T').restrictScalars T) (Algebra.linearMap T T')
    (fun x hx => h ▸ Ideal.mem_map_of_mem _ hx)

theorem a3b4g_quotientLocalizationMap_isLocalizedModule (J : Ideal T) (J' : Ideal T')
    (h : J' = J.map (algebraMap T T')) :
    IsLocalizedModule S (a3b4g_quotientLocalizationMap J J' h) where
  map_units s := a3b4g_isUnit_algebraMap_end (T' := T') S s
  surj y := by
    induction y using Submodule.Quotient.induction_on with
    | _ z =>
      obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj S z
      refine ⟨⟨Submodule.Quotient.mk x, s⟩, ?_⟩
      change s • Submodule.Quotient.mk z = Submodule.Quotient.mk _
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      simp only [Submonoid.smul_def, Algebra.smul_def, Algebra.linearMap_apply]
      rw [mul_comm]
      exact hxs
  exists_of_eq {a b} hab := by
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hab
      rw [Submodule.Quotient.eq] at hab
      simp only [Submodule.restrictScalars_mem, Algebra.linearMap_apply] at hab
      rw [h, ← map_sub] at hab
      obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff S T').mp hab
      rw [← map_mul] at hys
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists S T').mp hys
      refine ⟨c * s, ?_⟩
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      simp only [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul]
      have : ((c : T) * s) * (a - b) = c * y := by rw [← hc]; ring
      rw [← mul_sub, this]
      exact Ideal.mul_mem_left _ _ y.2

include S in
/-- Free graded pieces of the filtration by the powers of `I` localize to free graded pieces of
the same rank for the extended ideal. Source: Atiyah–Macdonald, *Introduction to Commutative
Algebra*, Proposition 3.3. -/
theorem a3b4g_graded_free_localization (I : Ideal T) (k r : ℕ)
    (e : a3b4g_gradedPiece (fun k => ((I ^ k : Ideal T) : Submodule T T)) k ≃ₗ[T]
      (Fin r → T ⧸ I)) :
    Nonempty (a3b4g_gradedPiece
      (fun k => (((I.map (algebraMap T T')) ^ k : Ideal T') : Submodule T' T')) k ≃ₗ[T']
        (Fin r → T' ⧸ I.map (algebraMap T T'))) := by
  let φ := a3b4g_gradedLocalizationMap (T' := T') (I ^ k) (I ^ (k + 1))
    ((I.map (algebraMap T T')) ^ k) ((I.map (algebraMap T T')) ^ (k + 1))
    (Ideal.map_pow _ _ _).symm (Ideal.map_pow _ _ _).symm
  have : IsLocalizedModule S φ := a3b4g_gradedLocalizationMap_isLocalizedModule S _ _ _ _ _ _
  let q := a3b4g_quotientLocalizationMap (T' := T') I (I.map (algebraMap T T')) rfl
  have : IsLocalizedModule S q := a3b4g_quotientLocalizationMap_isLocalizedModule S _ _ _
  let ψ : (Fin r → T ⧸ I) →ₗ[T] (Fin r → T' ⧸ I.map (algebraMap T T')) :=
    LinearMap.pi fun j => q ∘ₗ LinearMap.proj j
  have : IsLocalizedModule S ψ := IsLocalizedModule.pi S (fun _ => q)
  have : IsLocalizedModule S (ψ ∘ₗ e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S ψ e
  exact ⟨(IsLocalizedModule.linearEquiv S φ (ψ ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization
    S T'⟩

end HodgeLean.Adapters

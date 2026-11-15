import HodgeLean.Foundations.Program.G32SelectedRealizationCyclotomic

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_kernel_fixed_stable {H K V : Type*} [Group H] [CommGroup K]
    [AddCommGroup V] [Module ℚ V] (R : Representation ℚ H V) (χ : H →* K)
    (a : H) (v : V) (hv : ∀ h, χ h = 1 → R h v = v) :
    ∀ h, χ h = 1 → R h (R a v) = R a v := by
  intro h hh
  have hh' : χ (a⁻¹ * h * a) = 1 := by
    rw [map_mul, map_mul, map_inv, hh, mul_one, inv_mul_cancel]
  calc
    R h (R a v) = R (h * a) v := by rw [map_mul, Module.End.mul_apply]
    _ = R (a * (a⁻¹ * h * a)) v := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
    _ = R a (R (a⁻¹ * h * a) v) := by rw [map_mul, Module.End.mul_apply]
    _ = R a v := by rw [hv _ hh']

theorem g32y_fixed_character_power {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℚ V] {m : ℕ} [NeZero m]
    (R : Representation ℚ H V) (χ : H →* Multiplicative (ZMod m))
    (a : H) (ha : χ a = Multiplicative.ofAdd 1)
    (v : V) (hv : ∀ h, χ h = 1 → R h v = v) (h : H) :
    R h v = (R a ^ (χ h).toAdd.val) v := by
  let k := (χ h).toAdd.val
  have hpow : χ (a ^ k) = χ h := by
    apply Multiplicative.toAdd.injective
    rw [map_pow, ha, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
    exact ZMod.natCast_zmod_val (χ h).toAdd
  have hh : χ ((a ^ k)⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, hpow, inv_mul_cancel]
  have hx : R h v = R (a ^ k) v := by
    calc
      R h v = R (a ^ k * ((a ^ k)⁻¹ * h)) v := by rw [mul_inv_cancel_left]
      _ = R (a ^ k) (R ((a ^ k)⁻¹ * h) v) := by rw [map_mul, Module.End.mul_apply]
      _ = R (a ^ k) v := by rw [hv _ hh]
  simpa only [map_pow] using hx

theorem g32y_relation_space_stable {H K V : Type*} [Group H] [CommGroup K]
    [AddCommGroup V] [Module ℚ V] (R : Representation ℚ H V) (χ : H →* K)
    (k : K) (p : Polynomial ℚ) :
    let W : Submodule ℚ V :=
      (⨅ h, ⨅ (_ : χ h = 1), LinearMap.eqLocus (R h) LinearMap.id) ⊓
      ⨅ h, ⨅ (_ : χ h = k), LinearMap.ker (Polynomial.aeval (R h) p)
    ∀ a v, v ∈ W → R a v ∈ W := by
  dsimp only
  intro a v hv
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    LinearMap.id_apply, LinearMap.mem_ker] at hv ⊢
  refine ⟨g32y_kernel_fixed_stable R χ a v hv.1, ?_⟩
  intro b hb
  have hb' : χ (a⁻¹ * b * a) = k := by
    rw [map_mul, map_mul, map_inv, hb, mul_comm (χ a)⁻¹ k,
      mul_assoc, inv_mul_cancel, mul_one]
  have hc : R a ∘ₗ R (a⁻¹ * b * a) = R b ∘ₗ R a := by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
    congr 1
    group
  have hh := LinearMap.congr_fun
    (g32y_aeval_intertwine (R a) (R (a⁻¹ * b * a)) (R b) hc p) v
  simp only [LinearMap.comp_apply] at hh
  rw [hv.2 _ hb', map_zero] at hh
  exact hh.symm

theorem g32y_restrict_aeval_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (W : Submodule ℚ V) (hTW : ∀ v ∈ W, T v ∈ W)
    (p : Polynomial ℚ) (hp : ∀ v ∈ W, Polynomial.aeval T p v = 0) :
    Polynomial.aeval (T.restrict hTW) p = 0 := by
  let t : Module.End ℚ W := T.restrict hTW
  have hc : W.subtype ∘ₗ t = T ∘ₗ W.subtype := rfl
  have hh := g32y_aeval_intertwine W.subtype t T hc p
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change W.subtype (Polynomial.aeval t p v) = 0
  calc
    W.subtype (Polynomial.aeval t p v) = Polynomial.aeval T p (W.subtype v) :=
      LinearMap.congr_fun hh v
    _ = 0 := hp v v.property

end HodgeLean.Foundations.Program

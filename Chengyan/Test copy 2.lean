import Mathlib
open Ideal Padic Nat
open scoped algebraMap

theorem zpow_congr {L : Type*} [Field L] (ζ : L) (n : ℕ) [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    {a b : ℤ} : ζ ^ a = ζ ^ b ↔ (a:ZMod n) = (b:ZMod n) := by
  constructor
  · rintro h
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
    have h1:ζ^((b-a)) =1 := by
      rw [zpow_sub₀ hζ0,div_eq_one_iff_eq (zpow_ne_zero _ hζ0)]
      simp only[h]
    have h3: (n:Int) ∣ (b - a) := by
      rwa [hζ.zpow_eq_one_iff_dvd] at h1
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).mpr h3
  · rintro h
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
    rw[←div_eq_one_iff_eq (zpow_ne_zero _ hζ0),←zpow_sub₀ hζ0,hζ.zpow_eq_one_iff_dvd]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub b a n).mp (id (Eq.symm h))

theorem pow_congr {L : Type*} [Field L] (ζ : L) (n : ℕ) [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    {a b : ℕ} : ζ ^ a = ζ ^ b ↔ (a:ZMod n) = (b:ZMod n) := by
    convert zpow_congr ζ n hζ (a := a) (b := b) <;> simp

lemma isDomain_of_faithfulSMul (B L : Type*) [CommRing B] [CommRing L] [IsDomain L]
    [Algebra B L] [FaithfulSMul B L] : IsDomain B :=
  Function.Injective.isDomain (algebraMap B L) <| by
  rwa [← faithfulSMul_iff_algebraMap_injective B L]

lemma faithfulSMul_of_isIntegralClosure (A B L : Type*) [CommRing A] [CommSemiring B] [CommRing L]
    [Algebra A L] [Algebra B L] [IsIntegralClosure B A L] : FaithfulSMul B L where
  eq_of_smul_eq_smul {b₁ b₂} h := by
    apply IsIntegralClosure.algebraMap_injective B A L
    simp [Algebra.algebraMap_eq_smul_one, h 1]

lemma pow_notMem {B : Type*} [CommRing B](I : Ideal B) [hI : I.IsPrime]
    (ℓ : ℕ) (hlp : ↑ℓ ∉ I) (i:ℕ) : ↑(ℓ^i) ∉ I := by
  simpa using (hI.mem_of_pow_mem i).mt hlp

variable {A K L B G : Type*}
    -- let L be an algebraic closure of K
    [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    -- and let B be the integral closure of A in L
    [CommRing A] [CommRing B] [Algebra B L] [Algebra A L]
    [Algebra A B] [IsIntegralClosure B A L]
    -- Let G be the Galois group of L/K
    [Group G] [MulSemiringAction G L] [MulSemiringAction G B]
    [SMulCommClass G A B] [IsScalarTower G B L]
    -- Let F be an element of G
    (F : G)
    -- Let I be a prime ideal of B
    (I : Ideal B) (hI : I.IsPrime)
    -- assume F is a Frobenius element at I
    (hF : IsArithFrobAt A F I)
    -- Then for a prime ell not in I...
    (ℓ : ℕ) [Fact (Nat.Prime ℓ)](hlp : (ℓ : B) ∉ I)

open Polynomial in
lemma isIntegral_of_roots {n : ℕ} (hpos : 0 < n) {ζ : L} (hζ : ζ ^ n = 1) : IsIntegral ℤ ζ :=
  ⟨X ^ n - 1, monic_X_pow_sub_C 1 (Nat.ne_of_lt hpos).symm, by simp [hζ]⟩

lemma exists_isPrimitiveRoot (L : Type*) [Field L] [IsAlgClosed L]
    {B : Type*} [CommRing B] [Algebra B L] [FaithfulSMul B L]
    (hbl : (integralClosure ℤ L).toSubring ≤ (⊥ : Subalgebra B L).toSubring)
    {n : ℕ} [NeZero (n:L)] (hpos : 0 < n) : ∃ ζ : B, IsPrimitiveRoot ζ n := by
  obtain ⟨⟨ζ, hζ⟩, cyc⟩ := IsSepClosed.hasEnoughRootsOfUnity L n
  obtain ⟨ζ', hζ'⟩ := hbl (isIntegral_of_roots hpos hζ.pow_eq_one)
  exact ⟨ζ', IsPrimitiveRoot.of_map_of_injective (by simp_all [Algebra.ofId])
    (FaithfulSMul.algebraMap_injective B L)⟩

lemma hasEnoughRootsOfUnity (L : Type*) [Field L] [IsAlgClosed L]
    {B : Type*} [CommRing B] [Algebra B L] [FaithfulSMul B L]
    (hbl : (integralClosure ℤ L).toSubring ≤ (⊥ : Subalgebra B L).toSubring)
    (n : ℕ) [NeZero (n:L)] : HasEnoughRootsOfUnity B n :=
  have hpos : 0 < n := NeZero.pos_of_neZero_natCast L
  have := isDomain_of_faithfulSMul B L
  have : NeZero n := ⟨Nat.ne_of_gt hpos⟩
  ⟨exists_isPrimitiveRoot L hbl hpos, inferInstance⟩

lemma hasEnoughRootsOfUnity' (A L B : Type*) [Field L] [IsAlgClosed L]
    [CommRing B] [Algebra B L] [FaithfulSMul B L]
    [CommRing A] [Algebra A L] [IsIntegralClosure B A L] (n : ℕ) [NeZero (n:L)] :
    HasEnoughRootsOfUnity B n :=
  hasEnoughRootsOfUnity L (fun _ hx ↦
    (IsIntegralClosure.isIntegral_iff (R := A)).1 hx.tower_top) n

include hI hlp hF K B L
theorem cyclotomicCharacter_eq_card_quotient_under :
    ((cyclotomicCharacter L ℓ (MulSemiringAction.toRingEquiv G L F)) : ℤ_[ℓ]) =
    Nat.card (A ⧸ I.under A) := by
  have := faithfulSMul_of_isIntegralClosure A B L
  have := isDomain_of_faithfulSMul B L
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have (i : ℕ) : NeZero ((ℓ ^ i : ℕ) : B) := ⟨by aesop⟩
  have (i : ℕ) : NeZero ((ℓ ^ i : ℕ) : L) :=
    ⟨by simpa using (FaithfulSMul.algebraMap_eq_zero_iff B L).not.2 (this i).ne⟩
  set q := Nat.card (A ⧸ under A I)
  set g := MulSemiringAction.toRingEquiv G L F
  refine PadicInt.ext_of_toZModPow.1 fun i ↦ ?_
  obtain ⟨ζ, hζ⟩ := (hasEnoughRootsOfUnity' A L B (ℓ ^ i)).prim
  have hζ' : IsPrimitiveRoot (ζ : L) (ℓ ^ i) := IsPrimitiveRoot.map_of_injective hζ
    (FaithfulSMul.algebraMap_injective B L)
  have g_ζ_eq_ζ_pow_q : g ζ = ζ ^ q := by
    simpa [g, q, algebraMap.coe_smul] using congr(algebraMap B L
      $(AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hζ.pow_eq_one (pow_notMem I ℓ hlp i)))
  have pow_eq : (ζ : L) ^ ((cyclotomicCharacter L ℓ g).val.toZModPow i).val = ζ ^ q := by
    rw [← cyclotomicCharacter.spec ℓ g ζ hζ'.pow_eq_one, g_ζ_eq_ζ_pow_q]
  rw [pow_congr _ _ hζ'] at pow_eq
  simpa using pow_eq

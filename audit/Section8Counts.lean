import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Basic

/-! Numerical bounds, case predicates, and high-conductor summation for Section 8. -/
namespace SectionEight

private lemma valuation_one {n : ℕ} (h : n % 4 = 2) : padicValNat 2 n = 1 := by
  have nz : n ≠ 0 := by omega
  have lo : 1 ≤ padicValNat 2 n := (padicValNat_dvd_iff_le nz).mp (by
    simp only [pow_one]
    omega)
  have hi : ¬ 2 ≤ padicValNat 2 n := by
    intro hh
    have hd := (padicValNat_dvd_iff_le nz).mpr hh
    norm_num at hd
    omega
  omega

private lemma dyadic_part_le (n : ℕ) (hn : n ≠ 0) : 2 ^ padicValNat 2 n ≤ n := by
  rw [← Nat.factorization_def n Nat.prime_two]
  exact Nat.ordProj_le 2 hn

/-- Uniform in the odd base. The exponent may be any positive divisor of F. -/
theorem dyadic_power_bound {l f F : ℕ} (hl : 1 < l) (hodd : Odd l)
    (hf : 0 < f) (hF : 0 < F) (hdiv : f ∣ F) :
    2 ^ (l ^ f - 1).factorization 2 ≤ 2 ^ F.factorization 2 * (l + 1) := by
  have hp : 1 < l ^ f := Nat.one_lt_pow hf.ne' hl
  have hnp : ¬ 2 ∣ l := by have := Nat.odd_iff.mp hodd; omega
  have hplus : 0 < l ^ f + 1 := by omega
  have hminus : 0 < l ^ f - 1 := by omega
  have hdouble := padicValNat.pow_two_sub_one hl hnp
    (show 2 * f ≠ 0 by omega) (even_two_mul f)
  have hfac : l ^ (2 * f) - 1 = (l ^ f + 1) * (l ^ f - 1) := by
    rw [Nat.mul_comm 2 f, pow_mul]
    simpa using Nat.pow_two_sub_pow_two (l ^ f) 1
  rw [hfac, padicValNat.mul hplus.ne' hminus.ne',
      padicValNat.mul (by decide : 2 ≠ 0) hf.ne', padicValNat.self (by decide : 1 < 2)] at hdouble
  have hv : 1 ≤ padicValNat 2 (l ^ f + 1) := (padicValNat_dvd_iff_le hplus.ne').mp (by
    simpa only [pow_one, ← even_iff_two_dvd] using hodd.pow.add_one)
  have hFval : padicValNat 2 f ≤ padicValNat 2 F := by
    simpa only [← Nat.factorization_def _ Nat.prime_two] using
      ((Nat.factorization_le_iff_dvd hf.ne' hF.ne').mpr hdiv 2)
  have hmod := Nat.odd_iff.mp hodd
  have hcases : (l - 1) % 4 = 2 ∨ (l + 1) % 4 = 2 := by omega
  simp only [Nat.factorization_def _ Nat.prime_two]
  rcases hcases with h | h
  · have ht := valuation_one h
    calc 2 ^ padicValNat 2 (l ^ f - 1)
        ≤ 2 ^ (padicValNat 2 F + padicValNat 2 (l + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ 2 ^ padicValNat 2 F * (l + 1) := by
        rw [pow_add]
        exact Nat.mul_le_mul_left _ (dyadic_part_le _ (by omega))
  · have ht := valuation_one h
    calc 2 ^ padicValNat 2 (l ^ f - 1)
        ≤ 2 ^ (padicValNat 2 F + padicValNat 2 (l - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ 2 ^ padicValNat 2 F * (l + 1) := by
        rw [pow_add]
        exact Nat.mul_le_mul_left _ ((dyadic_part_le _ (by omega)).trans (by omega))


/-- The order used by the host divides a single totient determined by the base character. -/
theorem period_dvd {l a o : ℕ} (hl : l.Prime) (hodd : Odd l) (ho : 0 < o)
    (ha : a ∣ 2 * o) (hla : ¬ l ∣ a) :
    0 < orderOf (l : ZMod (Nat.lcm 4 a)) ∧
      orderOf (l : ZMod (Nat.lcm 4 a)) ∣ (4 * o).totient := by
  let M := Nat.lcm 4 a
  have hM : M ∣ 4 * o := Nat.lcm_dvd (dvd_mul_right 4 o) (ha.trans ⟨2, by ring⟩)
  have hMpos := Nat.pos_of_dvd_of_pos hM (by positivity : 0 < 4 * o)
  have l_ne_two : l ≠ 2 := by have := Nat.odd_iff.mp hodd; omega
  have cop : l.Coprime M := by
    apply hl.coprime_iff_not_dvd.mpr
    intro h
    have hla4 := h.trans (Nat.lcm_dvd (dvd_mul_right 4 a) (dvd_mul_left a 4))
    rcases hl.dvd_mul.mp hla4 with h4 | hh
    · have h2 : l ∣ 2 := hl.dvd_of_dvd_pow (show l ∣ 2 ^ 2 by simpa using h4)
      exact l_ne_two ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h2)
    · exact hla hh
  have hpow : (l : ZMod M) ^ M.totient = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient cop)
  have hd := orderOf_dvd_of_pow_eq_one hpow
  exact ⟨Nat.pos_of_dvd_of_pos hd (Nat.totient_pos.mpr hMpos), hd.trans (Nat.totient_dvd_of_dvd hM)⟩

private lemma rounded_power_le (n : ℕ) (hn : 0 < n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  by_cases h : n = 1
  · simp [h]
  have h1 : 1 < n := by omega
  have hpos := Nat.clog_pos (by decide : 1 < 2) h1
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 n = k + 1 := ⟨Nat.clog 2 n - 1, by omega⟩
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h1
  rw [hk] at hpred ⊢
  simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 hpred.le

/-- Both exact native powers of two divide one power chosen before the auxiliary character.
The parameter N is the working host modulus, M is the base conductor and P the fixed
auxiliary prime for case III. -/
theorem common_levels {l f F N M o P c : ℕ} (hl : 1 < l) (hodd : Odd l)
    (hf : 0 < f) (hF : 0 < F) (hfF : f ∣ F)
    (hN : 0 < N) (hM : 0 < M) (hP : 0 < P) (hc : 2 ^ c ≤ N) :
    let K := 2 ^ F.factorization 2
    let A := 64 * o * M ^ 2 + 4 * K ^ 2 * M * P + 8
    let n₀ := (l ^ f - 1).factorization 2
    let n₂ := Nat.clog 2 (max (l * N * 4 ^ n₀) (2 ^ (c + 6) * o * l ^ 3 * M ^ 2))
    let n₃ := Nat.clog 2 (max (l * M * P * 4 ^ n₀) (8 * l ^ 2))
    let D := 2 ^ Nat.clog 2 (A * N * l ^ 3)
    2 ^ n₂ ∣ D ∧ 2 ^ n₃ ∣ D ∧ D ≤ 2 * A * N * l ^ 3 ∧
      16 * o * (l * M) ^ 2 * 4 ^ n₀ ≤ 64 * o * M ^ 2 * K ^ 2 * l ^ 4 := by
  dsimp only
  let K := 2 ^ F.factorization 2
  let A := 64 * o * M ^ 2 + 4 * K ^ 2 * M * P + 8
  let n₀ := (l ^ f - 1).factorization 2
  have hval : 2 ^ n₀ ≤ K * (l + 1) := dyadic_power_bound hl hodd hf hF hfF
  have hval' : 2 ^ n₀ ≤ K * (2 * l) := hval.trans (Nat.mul_le_mul_left K (by omega))
  have h4 : 4 ^ n₀ ≤ 4 * K ^ 2 * l ^ 2 := by
    calc 4 ^ n₀ = (2 ^ n₀) ^ 2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; rfl
      _ ≤ (K * (2 * l)) ^ 2 := Nat.pow_le_pow_left hval' 2
      _ = 4 * K ^ 2 * l ^ 2 := by ring
  have hm : 4 * K ^ 2 * M * P ≤ A := by dsimp [A]; omega
  have hcst : 4 * K ^ 2 ≤ A := by
    refine le_trans ?_ hm
    calc 4 * K ^ 2 = 4 * K ^ 2 * 1 * 1 := by simp
      _ ≤ 4 * K ^ 2 * M * P := by gcongr <;> omega
  have hcst' : 64 * o * M ^ 2 ≤ A := by dsimp [A]; omega
  have h8 : 8 ≤ A := by dsimp [A]; omega
  have h2 : max (l * N * 4 ^ n₀) (2 ^ (c + 6) * o * l ^ 3 * M ^ 2) ≤ A * N * l ^ 3 := by
    apply max_le
    · calc l * N * 4 ^ n₀ ≤ l * N * (4 * K ^ 2 * l ^ 2) := Nat.mul_le_mul_left _ h4
        _ = (4 * K ^ 2) * N * l ^ 3 := by ring
        _ ≤ A * N * l ^ 3 := by gcongr
    · calc 2 ^ (c + 6) * o * l ^ 3 * M ^ 2 = (64 * o * M ^ 2) * 2 ^ c * l ^ 3 := by rw [pow_add]; ring
        _ ≤ A * N * l ^ 3 := by gcongr
  have h3 : max (l * M * P * 4 ^ n₀) (8 * l ^ 2) ≤ A * N * l ^ 3 := by
    apply max_le
    · calc l * M * P * 4 ^ n₀ ≤ l * M * P * (4 * K ^ 2 * l ^ 2) := Nat.mul_le_mul_left _ h4
        _ = (4 * K ^ 2 * M * P) * 1 * l ^ 3 := by ring
        _ ≤ A * N * l ^ 3 := by gcongr; omega
    · calc 8 * l ^ 2 = 8 * 1 * l ^ 2 := by simp
        _ ≤ A * N * l ^ 3 := by gcongr <;> omega
  refine ⟨Nat.pow_dvd_pow 2 (Nat.clog_mono_right 2 h2), Nat.pow_dvd_pow 2 (Nat.clog_mono_right 2 h3), ?_, ?_⟩
  · have hA : 0 < A := by omega
    have htotal : 0 < A * N * l ^ 3 := Nat.mul_pos (Nat.mul_pos hA hN) (pow_pos (by omega) 3)
    change 2 ^ Nat.clog 2 (A * N * l ^ 3) ≤ 2 * A * N * l ^ 3
    simpa only [Nat.mul_assoc] using rounded_power_le (A * N * l ^ 3) htotal
  · calc 16 * o * (l * M) ^ 2 * 4 ^ n₀ ≤ 16 * o * (l * M) ^ 2 * (4 * K ^ 2 * l ^ 2) := Nat.mul_le_mul_left _ h4
      _ = 64 * o * M ^ 2 * K ^ 2 * l ^ 4 := by ring

/-- The union of the native guards for II and III, after taking character orders.
Outside the exceptional set, resonance makes the prime-to-l component equal to the
original character. The only order excluded on this side is one. -/
theorem symplectic_range {exceptional : Prop} {l r ord ordP : ℕ} (hr : 0 < r)
    (large : ¬ exceptional → 5 ≤ l)
    (same : ¬ exceptional → l - 1 ∣ 2 * r → ordP = ord) :
    ((2 ≤ r ∧ Even ordP ∧ (exceptional ∨ l - 1 ∣ 2 * r)) ∨
      (¬ exceptional ∧ l - 1 ∣ 2 * r ∧ Odd ord ∧ ord ≠ 1)) ↔
    (¬ exceptional ∧ l - 1 ∣ 2 * r ∧ ord ≠ 1) ∨ (exceptional ∧ 2 ≤ r ∧ Even ordP) := by
  classical
  constructor
  · rintro (⟨hr2, hev, hx⟩ | ⟨hout, hres, _, hne⟩)
    · by_cases hE : exceptional
      · exact Or.inr ⟨hE, hr2, hev⟩
      · have hd := hx.resolve_left hE
        have he := (same hE hd) ▸ hev
        exact Or.inl ⟨hE, hd, fun h => by simp [h] at he⟩
    · exact Or.inl ⟨hout, hres, hne⟩
  · rintro (⟨hout, hres, hne⟩ | ⟨hexc, hr2, hev⟩)
    · have hlo := large hout
      have hsize := Nat.le_of_dvd (by omega : 0 < 2 * r) hres
      have hr2 : 2 ≤ r := by omega
      rcases Nat.even_or_odd ord with hev | hod
      · exact Or.inl ⟨hr2, (same hout hres).symm ▸ hev, Or.inr hres⟩
      · exact Or.inr ⟨hout, hres, hod, hne⟩
    · exact Or.inl ⟨hr2, hev, Or.inl hexc⟩


/-- An integer majorant for the native pre-count, using log p ≤ p.
The same bound applies to any native level d dividing the chosen rounded power. -/
theorem count_majorant {l N r P d p B o C a : ℕ}
    (hl : 0 < l) (hN : 0 < N) (hr : 0 < r) (hd : d ≤ 2 * B * N * l ^ 3)
    (hp : p ≤ 6 * l * N * P + 1) :
    2 * C * ((l - 1) * d * (2 * o)) * ((l * d * N * P) * (r + 1)) ^ a * p ≤
      (8 * C * o * B * (4 * B * P) ^ a * (6 * P + 1)) * (l * N * r) ^ (4 * a + 5) := by
  let X := l * N * r
  have hX : 0 < X := Nat.mul_pos (Nat.mul_pos hl hN) hr
  have hLN : l * N ≤ X := Nat.le_mul_of_pos_right _ hr
  have hlX : l ≤ X := (Nat.le_mul_of_pos_right l hN).trans hLN
  have hdX : d ≤ 2 * B * X ^ 3 := by
    calc d ≤ 2 * B * N * l ^ 3 := hd
      _ ≤ 2 * B * N ^ 3 * l ^ 3 := by
        have hn : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
        gcongr
      _ = 2 * B * (l * N) ^ 3 := by ring
      _ ≤ 2 * B * X ^ 3 := by gcongr
  have hk : (l - 1) * d * (2 * o) ≤ 4 * o * B * X ^ 4 := by
    calc (l - 1) * d * (2 * o) ≤ X * (2 * B * X ^ 3) * (2 * o) :=
           Nat.mul_le_mul_right _ (Nat.mul_le_mul ((Nat.sub_le l 1).trans hlX) hdX)
      _ = 4 * o * B * X ^ 4 := by ring
  have hL : l * d * N * P * (r + 1) ≤ (4 * B * P) * X ^ 4 := by
    calc l * d * N * P * (r + 1) ≤ l * d * N * P * (2*r) := by gcongr; omega
      _ = (2 * P) * d * X := by dsimp [X]; ring
      _ ≤ (2 * P) * (2 * B * X ^ 3) * X := by gcongr
      _ = (4 * B * P) * X ^ 4 := by ring
  have hpX : p ≤ (6 * P + 1) * X := by
    calc p ≤ 6 * l * N * P + 1 := hp
      _ = 6 * P * (l*N) + 1 := by ring
      _ ≤ 6 * P * X + X := Nat.add_le_add (Nat.mul_le_mul_left _ hLN) hX
      _ = (6 * P + 1) * X := by ring
  calc
    _ ≤ 2 * C * (4 * o * B * X ^ 4) * ((4 * B * P) * X ^ 4) ^ a * ((6*P+1)*X) := by gcongr
    _ = (8 * C * o * B * (4 * B * P) ^ a * (6 * P + 1)) * X ^ (4 * a + 5) := by
      rw [mul_pow (4 * B * P) (X ^ 4) a, ← pow_mul X 4 a, pow_add X (4*a) 5]
      ring


/-- The Gaussian threshold bounds the residue characteristic on a fixed host. -/
theorem high_prime {l o M n b N : ℕ} (ho : 0 < o) (hM : 0 < M)
    (threshold : 16 * o * (l * M)^2 * 4^n ≤ 2^b) (conductor : 2^b ≤ N) :
    l^2 ≤ N := by
  calc l^2 = 1 * (l * 1)^2 * 1 := by simp
    _ ≤ 16 * o * (l * M)^2 * 4^n := Nat.mul_le_mul
      (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.mul_le_mul_left l hM) 2))
      (by have hp : 0 < (4 : ℕ)^n := pow_pos (by decide) n; exact hp)
    _ ≤ N := threshold.trans conductor

/-- The last step of the Gaussian count, with the normalized arithmetic length. -/
theorem gaussian_pointwise {raw : ℕ∞} {v e : ℕ} {s w X : ℝ} {a : ℕ}
    (he : 0 < e) (hw : 0 ≤ w) (hX : 2 ≤ X) (finite_bound : raw ≤ (v : ℕ∞))
    (trace_bound : (v : ℝ) ≤ 2 * e * s) (height_bound : s * w ≤ X ^ a) :
    raw ≠ ⊤ ∧ (raw.toNat : ℝ) / e * w ≤ X ^ (a + 1) := by
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top v) finite_bound, ?_⟩
  have hlen : (raw.toNat : ℝ) ≤ v := by exact_mod_cast ENat.toNat_le_of_le_natCast finite_bound
  have hdiv : (raw.toNat : ℝ) / e ≤ 2 * s := by
    apply (div_le_iff₀ (by exact_mod_cast he : 0 < (e : ℝ))).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hlen.trans trace_bound
  calc (raw.toNat : ℝ) / e * w ≤ (2 * s) * w := mul_le_mul_of_nonneg_right hdiv hw
    _ ≤ 2 * X ^ a := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left height_bound (by norm_num)
    _ ≤ X ^ (a + 1) := by rw [pow_succ, mul_comm (X ^ a) X]; gcongr

/-- Sum over the active primes in any finite prime set, once the high cutoff
has shown that they lie in [1,N]. Character types may vary with the prime. -/
theorem high_mass {ι : ℕ → Type*} {N t a : ℕ} (hN : 0 < N) (ht : 0 < t)
    (S : Finset ℕ) (active : S ⊆ Finset.Icc 1 N)
    (T : (l : ℕ) → ℕ → Finset (ι l)) (mass : (l : ℕ) → ℕ → ι l → ℝ)
    (card : ∀ l ∈ S, ∀ r ∈ Finset.Ico 1 t, (T l r).card ≤ N)
    (bound : ∀ l ∈ S, ∀ r ∈ Finset.Ico 1 t, ∀ i ∈ T l r, mass l r i ≤ ((l : ℝ) * N * r)^a) :
    ∑ l ∈ S, ∑ r ∈ Finset.Ico 1 t, ∑ i ∈ T l r, mass l r i ≤ ((N : ℝ)*t)^(2*a+2) := by
  let X : ℝ := (N : ℝ) * t
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have x0 : 0 ≤ X := by dsimp [X]; positivity
  have nx : (N : ℝ) ≤ X := le_mul_of_one_le_right (by positivity) htr
  have hs : S.card ≤ N := by simpa using Finset.card_le_card active
  have hr : (Finset.Ico 1 t).card ≤ t := by simp
  have trm (l : ℕ) (hl : l ∈ S) (r : ℕ) (h : r ∈ Finset.Ico 1 t) (i : ι l) (hi : i ∈ T l r) :
      mass l r i ≤ X ^ (2*a) := by
    have hl' : (l : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp (active hl)).2
    have hr' : (r : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Ico.mp h).2.le
    have hsize : (l : ℝ) * N * r ≤ X^2 := by
      calc (l : ℝ) * N * r ≤ N * ((N : ℝ)*t) := by rw [← mul_assoc]; gcongr
        _ = (N : ℝ)*X := rfl
        _ ≤ X^2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right nx x0
    calc mass l r i ≤ ((l : ℝ) * N * r)^a := bound l hl r h i hi
      _ ≤ (X^2)^a := pow_le_pow_left₀ (by positivity) hsize a
      _ = X^(2*a) := (pow_mul X 2 a).symm
  have charSum (l : ℕ) (hl : l ∈ S) (r : ℕ) (h : r ∈ Finset.Ico 1 t) :
      (∑ i ∈ T l r, mass l r i) ≤ (N : ℝ) * X^(2*a) := by
    calc _ ≤ ∑ _i ∈ T l r, X^(2*a) := Finset.sum_le_sum fun i hi => trm l hl r h i hi
      _ = ((T l r).card : ℝ) * X^(2*a) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card l hl r h) (pow_nonneg x0 _)
  calc
    _ ≤ ∑ _l ∈ S, ∑ _r ∈ Finset.Ico 1 t, (N : ℝ) * X^(2*a) :=
       Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun r h => charSum l hl r h
    _ = (S.card : ℝ) * ((Finset.Ico 1 t).card : ℝ) * N * X^(2*a) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (N : ℝ) * t * X * X^(2*a) := by
      gcongr
    _ = X^(2*a+2) := by change X * X * X^(2*a) = _; rw [pow_add, pow_two]; ring

end SectionEight

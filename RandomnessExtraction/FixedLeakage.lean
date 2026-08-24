import RandomnessExtraction.OutputMonotonicity
import RandomnessExtraction.Specializations

/-!
# Fixed-leakage inversions

Integer output lengths are represented by powers of two.  The paper's
supremum is taken in `ℕ ∪ {+∞}`.  The proofs below establish eventual
boundedness under the hypotheses of Corollary 2 before taking the finite part.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit OneShot

set_option maxHeartbeats 800000

theorem information_nonneg {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (x : X) (y : Y) : 0 ≤ information P x y := by
  unfold information
  exact neg_nonneg.mpr (Real.logb_nonpos (by norm_num)
    ((P.conditional y).nonneg x) ((P.conditional y).apply_le_one x))

theorem fiberEntropy_nonneg {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (y : Y) : 0 ≤ fiberEntropy P y :=
  (P.conditional y).expect_nonneg (information_nonneg P · y)

theorem entropy_nonneg {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) : 0 ≤ entropy P :=
  P.marginal.expect_nonneg (fiberEntropy_nonneg P)

theorem entropy_pos_of_totalVariance_pos
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV : 0 < totalVariance P) : 0 < entropy P := by
  apply lt_of_le_of_ne (entropy_nonneg P)
  intro hH
  have hH0 : entropy P = 0 := hH.symm
  have hfiber (y : Y) : fiberEntropy P y = 0 := by
    have hterm : P.marginal y * fiberEntropy P y ≤ entropy P := by
      rw [entropy, FinProb.expect]
      exact Finset.single_le_sum
        (fun z _ => mul_nonneg (P.marginal.nonneg z) (fiberEntropy_nonneg P z))
        (Finset.mem_univ y)
    have : P.marginal y * fiberEntropy P y = 0 :=
      le_antisymm (by simpa [hH0] using hterm)
        (mul_nonneg (P.marginal.nonneg y) (fiberEntropy_nonneg P y))
    exact (mul_eq_zero.mp this).resolve_left (hpY y).ne'
  have hinfo (x : X) (y : Y) : information P x y = 0 := by
    by_cases hp : P.conditional y x = 0
    · simp [information, hp, Real.logb]
    · have hppos : 0 < P.conditional y x :=
        lt_of_le_of_ne ((P.conditional y).nonneg x) (Ne.symm hp)
      have hterm : P.conditional y x * information P x y ≤ fiberEntropy P y := by
        rw [fiberEntropy, FinProb.expect]
        exact Finset.single_le_sum
          (fun z _ => mul_nonneg ((P.conditional y).nonneg z)
            (information_nonneg P z y)) (Finset.mem_univ x)
      have hz : P.conditional y x * information P x y = 0 :=
        le_antisymm (by simpa [hfiber y] using hterm)
          (mul_nonneg ((P.conditional y).nonneg x) (information_nonneg P x y))
      exact (mul_eq_zero.mp hz).resolve_left hppos.ne'
  have hV1 : variance₁ P = 0 := by
    rw [variance₁, hH0]
    simp [hfiber]
  have hV2 : variance₂ P = 0 := by
    rw [variance₂, FinProb.expect]
    apply Finset.sum_eq_zero
    intro y _
    rw [fiberVariance, hfiber y]
    simp [hinfo]
  rw [totalVariance, hV1, hV2] at hV
  linarith

/-- Integer output length obtained by rounding a prescribed second-order
rate down. -/
noncomputable def roundedBitLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (L : ℝ) (n : ℕ) : ℕ :=
  ⌊max 0 (n * entropy P + Real.sqrt n * L)⌋₊

noncomputable def roundedOutputSize
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (L : ℝ) (n : ℕ) : ℕ :=
  2 ^ roundedBitLength P L n

private theorem rawRate_eventually_nonneg
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hH : 0 < entropy P) (L : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ n * entropy P + Real.sqrt n * L := by
  by_cases hL : 0 ≤ L
  · filter_upwards with n
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hH.le)
      (mul_nonneg (Real.sqrt_nonneg _) hL)
  · have hneg : 0 < -L := neg_pos.mpr (lt_of_not_ge hL)
    obtain ⟨N : ℕ, hN : (-L / entropy P) ^ 2 ≤ N⟩ :=
      exists_nat_ge ((-L / entropy P) ^ 2)
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hratio : 0 ≤ -L / entropy P := div_nonneg hneg.le hH.le
    have hsquare : (-L / entropy P) ^ 2 ≤ (n : ℝ) := by
      exact hN.trans (by exact_mod_cast hnN)
    have hsqrt : -L / entropy P ≤ Real.sqrt n := by
      rw [← Real.sqrt_sq hratio]
      exact Real.sqrt_le_sqrt hsquare
    have hs : Real.sqrt n * (-L) ≤ (n : ℝ) * entropy P := by
      have hm := mul_le_mul_of_nonneg_right hsqrt hH.le
      have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg n)
      field_simp [hH.ne'] at hm
      nlinarith [hsqrtSq]
    nlinarith

theorem roundedBitLength_rate
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hH : 0 < entropy P) (L : ℝ) :
    Tendsto (fun n ↦
      ((roundedBitLength P L n : ℝ) - n * entropy P) / Real.sqrt n)
      atTop (nhds L) := by
  have hinvSqrt : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  have hzero := rawRate_eventually_nonneg P hH L
  have hdist : ∀ᶠ n : ℕ in atTop,
      dist (((roundedBitLength P L n : ℝ) - n * entropy P) / Real.sqrt n) L ≤
        (Real.sqrt (n : ℝ))⁻¹ := by
    filter_upwards [hzero, eventually_gt_atTop (0 : ℕ)] with n hraw hn
    let a := n * entropy P + Real.sqrt n * L
    have ha : 0 ≤ a := hraw
    have hfloorLe : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
    have haLt : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [Real.dist_eq]
    rw [roundedBitLength, max_eq_right hraw]
    change |(((⌊a⌋₊ : ℝ) - n * entropy P) / Real.sqrt n) - L| ≤ _
    have hid : (((⌊a⌋₊ : ℝ) - n * entropy P) / Real.sqrt n) - L =
        ((⌊a⌋₊ : ℝ) - a) / Real.sqrt n := by
      dsimp [a]
      field_simp [hs.ne']
      ring
    rw [hid, abs_div, abs_of_pos hs, abs_of_nonpos (sub_nonpos.mpr hfloorLe)]
    rw [inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hs).2 (by linarith)
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hdist hinvSqrt

theorem roundedOutputSize_rate
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hH : 0 < entropy P) (L : ℝ) :
    SecondOrderRate P (roundedOutputSize P L) L := by
  have h := roundedBitLength_rate P hH L
  apply h.congr'
  filter_upwards with n
  unfold roundedOutputSize
  rw [Nat.cast_pow, Real.logb_pow]
  norm_num

noncomputable def extendedNatSup (A : Set ℕ) : WithTop ℕ :=
  ⨆ ell ∈ A, (ell : WithTop ℕ)

/-- Equations (13)--(14): power-of-two output length at leakage budget `δ`,
with the supremum taken in `ℕ ∪ {+∞}` exactly as in the paper. -/
noncomputable def fixedLeakageLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (δ : ℝ) (P : FiniteSource X Y) : WithTop ℕ :=
  extendedNatSup {ell : ℕ | optimalFixedLeakage f P (2 ^ ell) ≤ δ}

noncomputable def optimizedLeakageLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (δ : ℝ) (P : FiniteSource X Y) : WithTop ℕ :=
  extendedNatSup {ell : ℕ | optimalOptimizedLeakage f P (2 ^ ell) ≤ δ}

private noncomputable def oneOutputHash
    {X : Type} [Fintype X] : SeededHash X (Fin 1) 1 where
  seed := FinProb.uniformFin 1 (by omega)
  hash := fun _ _ => 0

private theorem oneOutputHash_fixedLeakage
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) :
    fixedLeakage f P (oneOutputHash (X := X)) = 0 := by
  unfold fixedLeakage FinProb.expect
  simp only [Fintype.sum_unique, Nat.cast_one, inv_one, one_mul]
  rw [show (oneOutputHash (X := X)).seed default = 1 by
    simp [oneOutputHash, FinProb.uniformFin]]
  simp only [one_mul]
  apply Finset.sum_eq_zero
  intro y _
  have hout : outputMass (oneOutputHash (X := X)) (P.conditional y)
      default default = 1 := by
    unfold outputMass SeededHash.binMass oneOutputHash
    simpa using (P.conditional y).sum_prob
  rw [hout, f.map_one, mul_zero]

private theorem optimalFixedLeakage_one_le_zero
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) :
    optimalFixedLeakage f P 1 ≤ 0 := by
  simpa [oneOutputHash_fixedLeakage] using
    (optimalFixedLeakage_le_family f P (oneOutputHash (X := X)) (by omega))

private theorem oneOutputHash_referenceLeakage
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) :
    referenceLeakage f P (oneOutputHash (X := X))
      (P.marginal.prod (oneOutputHash (X := X)).seed) = 0 := by
  unfold referenceLeakage
  simp only [Fintype.sum_unique, Nat.cast_one, inv_one, one_mul]
  apply Finset.sum_eq_zero
  intro y _
  have hout : outputMass (oneOutputHash (X := X)) (P.conditional y)
      default default = 1 := by
    unfold outputMass SeededHash.binMass oneOutputHash
    simpa using (P.conditional y).sum_prob
  rw [hout]
  simpa [oneOutputHash, FinProb.prod_apply] using
    (perspective_self f (P.marginal.nonneg y))

private theorem optimalOptimizedLeakage_one_le_zero
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) :
    optimalOptimizedLeakage f P 1 ≤ 0 := by
  let H := oneOutputHash (X := X)
  calc
    optimalOptimizedLeakage f P 1 ≤ optimizedLeakage f P H :=
      optimalOptimizedLeakage_le_family f P H (by omega)
    _ ≤ referenceLeakage f P H (P.marginal.prod H.seed) :=
      optimizedLeakage_le_reference f P H (by omega) _
    _ = 0 := oneOutputHash_referenceLeakage f P

/-- The ordinary inverse of the strictly decreasing Gaussian profile, defined
by its unique level-set point. -/
noncomputable def gaussianProfileInverse
    (f : AdmissibleGenerator) (r δ : ℝ) : ℝ :=
  if h : ∃ x : ℝ, gaussianProfile f r x = δ then Classical.choose h else 0

theorem exists_unique_gaussianProfile_level
    (f : AdmissibleGenerator) {r δ : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hstrict : StrictAntiOn f (Set.Ioo 0 1))
    (hδ0 : 0 < δ) (hδf : δ < f 0) :
    ∃! x : ℝ, gaussianProfile f r x = δ := by
  let F := gaussianProfile f r
  have hreg := paperLemma19 f hr
  have haEv : ∀ᶠ x : ℝ in atBot, δ < F x :=
    hreg.2.2.1.eventually (Ioi_mem_nhds hδf)
  obtain ⟨a, ha⟩ := haEv.exists
  have hbEv : ∀ᶠ x : ℝ in atTop, F x < δ :=
    hreg.2.2.2.1.eventually (Iio_mem_nhds hδ0)
  obtain ⟨b, hb, hab⟩ := (hbEv.and (eventually_ge_atTop a)).exists
  have hmem : δ ∈ Set.Icc (F b) (F a) := ⟨hb.le, ha.le⟩
  obtain ⟨x, _, hx⟩ :=
    (intermediate_value_Icc' hab hreg.1.continuousOn hmem)
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact (hreg.2.2.2.2.1 hstrict).injective (hz.trans hx.symm)

theorem gaussianProfileInverse_spec
    (f : AdmissibleGenerator) {r δ : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hstrict : StrictAntiOn f (Set.Ioo 0 1))
    (hδ0 : 0 < δ) (hδf : δ < f 0) :
    gaussianProfile f r (gaussianProfileInverse f r δ) = δ := by
  unfold gaussianProfileInverse
  have hex : ∃ x : ℝ, gaussianProfile f r x = δ :=
    (exists_unique_gaussianProfile_level f hr hstrict hδ0 hδf).exists
  rw [dif_pos hex]
  exact Classical.choose_spec hex

private theorem leakageLength_inversion
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hH : 0 < entropy P)
    (V δ x : ℝ) (hV : 0 < V)
    (g : ℕ → ℕ → ℝ)
    (hmono : ∀ n, Monotone (g n))
    (hzero : ∀ n, g n 0 ≤ δ)
    (F : ℝ → ℝ) (hFstrict : StrictAnti F) (hFx : F x = δ)
    (hlimit : ∀ L : ℝ, Tendsto
      (fun n => g n (roundedBitLength P L n)) atTop
      (nhds (F (-L / Real.sqrt V)))) :
    Tendsto (fun n =>
      ((((extendedNatSup {ell : ℕ | g n ell ≤ δ}).untopD 0 : ℕ) : ℝ) -
        n * entropy P) / Real.sqrt n)
      atTop (nhds (-Real.sqrt V * x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let sV := Real.sqrt V
  have hsV : 0 < sV := Real.sqrt_pos.2 hV
  let η := ε / (4 * sV)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hsV)
  let Llo := -sV * (x + η)
  let Lhi := -sV * (x - η)
  let klo := roundedBitLength P Llo
  let khi := roundedBitLength P Lhi
  have hFlo : F (-Llo / sV) < δ := by
    have hid : -Llo / sV = x + η := by
      dsimp [Llo]
      field_simp [hsV.ne']
    rw [hid, ← hFx]
    exact hFstrict (lt_add_of_pos_right x hη)
  have hFhi : δ < F (-Lhi / sV) := by
    have hid : -Lhi / sV = x - η := by
      dsimp [Lhi]
      field_simp [hsV.ne']
    rw [hid, ← hFx]
    exact hFstrict (sub_lt_self x hη)
  have hloGood : ∀ᶠ n in atTop, g n (klo n) ≤ δ :=
    (hlimit Llo).eventually (Iio_mem_nhds hFlo) |>.mono fun _ h => h.le
  have hhiBad : ∀ᶠ n in atTop, δ < g n (khi n) :=
    (hlimit Lhi).eventually (Ioi_mem_nhds hFhi)
  have hklo := roundedBitLength_rate P hH Llo
  have hkhi := roundedBitLength_rate P hH Lhi
  have hkloNear : ∀ᶠ n in atTop,
      dist (((klo n : ℝ) - n * entropy P) / Real.sqrt n) Llo < ε / 4 :=
    hklo.eventually (Metric.ball_mem_nhds _ (div_pos hε (by norm_num)))
  have hkhiNear : ∀ᶠ n in atTop,
      dist (((khi n : ℝ) - n * entropy P) / Real.sqrt n) Lhi < ε / 4 :=
    hkhi.eventually (Metric.ball_mem_nhds _ (div_pos hε (by norm_num)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hloGood.and (hhiBad.and
    (hkloNear.and (hkhiNear.and (eventually_gt_atTop (0 : ℕ))))))
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hgood, hbad, hloNear, hhiNear, hn0⟩
  let A : Set ℕ := {ell | g n ell ≤ δ}
  have hA0 : (0 : ℕ) ∈ A := hzero n
  have hAbdd : BddAbove A := by
    refine ⟨khi n, ?_⟩
    intro ell hell
    by_contra hnot
    have hkell : khi n ≤ ell := Nat.le_of_not_ge hnot
    have := (hmono n hkell).trans hell
    exact (not_le_of_gt hbad) this
  have hloSup : klo n ≤ sSup A := le_csSup hAbdd hgood
  have hsupMem : sSup A ∈ A := Nat.sSup_mem ⟨0, hA0⟩ hAbdd
  have hext : extendedNatSup A = ((sSup A : ℕ) : WithTop ℕ) := by
    exact (WithTop.coe_sSup hAbdd).symm
  have hfinite : (extendedNatSup A).untopD 0 = sSup A := by
    rw [hext]
    rfl
  have hsupHi : sSup A < khi n := by
    by_contra hnot
    have hk : khi n ≤ sSup A := Nat.le_of_not_gt hnot
    exact (not_le_of_gt hbad) ((hmono n hk).trans hsupMem)
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  have hloNorm : ((klo n : ℝ) - n * entropy P) / Real.sqrt n ≤
      ((sSup A : ℕ) - n * entropy P) / Real.sqrt n := by
    apply (div_le_div_iff_of_pos_right hsqrtn).2
    have hc : (klo n : ℝ) ≤ (sSup A : ℕ) := by exact_mod_cast hloSup
    linarith
  have hhiNorm : ((sSup A : ℕ) - n * entropy P) / Real.sqrt n <
      ((khi n : ℝ) - n * entropy P) / Real.sqrt n := by
    apply (div_lt_div_iff_of_pos_right hsqrtn).2
    have hc : (sSup A : ℕ) < (khi n : ℝ) := by exact_mod_cast hsupHi
    linarith
  rw [Real.dist_eq, abs_lt] at hloNear
  rw [Real.dist_eq, abs_lt] at hhiNear
  rw [Real.dist_eq, abs_lt]
  rw [hfinite]
  have heta : sV * η = ε / 4 := by
    dsimp [η]
    field_simp [hsV.ne']
  dsimp [Llo, Lhi] at hloNear hhiNear
  change -ε < ((sSup A : ℕ) - n * entropy P) / Real.sqrt n -
      -Real.sqrt V * x ∧
    ((sSup A : ℕ) - n * entropy P) / Real.sqrt n -
      -Real.sqrt V * x < ε
  constructor <;> nlinarith

/-- **Corollary 2 (fixed-leakage `f`-expansions, fixed and optimized
marginals).** -/
theorem paperCorollary2
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (hstrict : StrictAntiOn f (Set.Ioo 0 1))
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (δ : ℝ) (hδ0 : 0 < δ) (hδf : δ < f 0)
    (hV : 0 < totalVariance P) :
    Tendsto (fun n =>
      ((((fixedLeakageLength f δ (blockSource P n)).untopD 0 : ℕ) : ℝ) -
        n * entropy P) /
        Real.sqrt n) atTop
      (nhds (-Real.sqrt (totalVariance P) * gaussianProfileInverse f
        (variance₁ P / totalVariance P) δ)) ∧
    Tendsto (fun n =>
      ((((optimizedLeakageLength f δ (blockSource P n)).untopD 0 : ℕ) : ℝ) -
        n * entropy P) /
        Real.sqrt n) atTop
      (nhds (-Real.sqrt (totalVariance P) * gaussianProfileInverse f 0 δ)) := by
  have hH := entropy_pos_of_totalVariance_pos P hpY hV
  have hr := varianceRatio_mem_unit P hV
  let r := variance₁ P / totalVariance P
  let xd := gaussianProfileInverse f r δ
  let xu := gaussianProfileInverse f 0 δ
  have hxd : gaussianProfile f r xd = δ :=
    gaussianProfileInverse_spec f hr hstrict hδ0 hδf
  have hxu : gaussianProfile f 0 xu = δ :=
    gaussianProfileInverse_spec f (by constructor <;> norm_num) hstrict hδ0 hδf
  have hFd : StrictAnti (gaussianProfile f r) :=
    strictAnti_gaussianProfile f hr.1 hr.2 hstrict
  have hFu : StrictAnti (gaussianProfile f 0) :=
    strictAnti_gaussianProfile f (by norm_num) (by norm_num) hstrict
  constructor
  · simpa [fixedLeakageLength, xd, r] using
      (leakageLength_inversion P hH (totalVariance P) δ xd hV
        (fun n ell => optimalFixedLeakage f (blockSource P n) (2 ^ ell))
        (fun n => monotone_nat_of_le_succ fun ell =>
          optimalFixedLeakage_pow_two_monotone f (blockSource P n) ell)
        (fun n => by simpa using
          (optimalFixedLeakage_one_le_zero f (blockSource P n)).trans hδ0.le)
        (gaussianProfile f r) hFd hxd (fun L => by
          have hmain := paperTheorem1 hBE f P hpY (roundedOutputSize P L)
            (fun n => pow_pos (by omega) _) L hV (roundedOutputSize_rate P hH L)
          simpa [roundedOutputSize, r] using hmain.1))
  · simpa [optimizedLeakageLength, xu] using
      (leakageLength_inversion P hH (totalVariance P) δ xu hV
        (fun n ell => optimalOptimizedLeakage f (blockSource P n) (2 ^ ell))
        (fun n => monotone_nat_of_le_succ fun ell =>
          optimalOptimizedLeakage_pow_two_monotone f (blockSource P n) ell)
        (fun n => by simpa using
          (optimalOptimizedLeakage_one_le_zero f (blockSource P n)).trans hδ0.le)
        (gaussianProfile f 0) hFu hxu (fun L => by
          have hmain := paperTheorem1 hBE f P hpY (roundedOutputSize P L)
            (fun n => pow_pos (by omega) _) L hV (roundedOutputSize_rate P hH L)
          simpa [roundedOutputSize, gaussianProfile_zero] using hmain.2.1))

end RandomnessExtraction

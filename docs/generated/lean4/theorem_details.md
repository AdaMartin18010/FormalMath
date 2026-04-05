---
msc_primary: 00A99
msc_secondary:
- 00A99
title: FormalMath 定理详细说明
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# FormalMath 定理详细说明

## fermat_coprime

**来源**: `docs\09-形式化证明\Lean4\InfinitudeOfPrimes.lean:153`

```lean4
theorem fermat_coprime {m n : ℕ} (hne : m ≠ n) : Nat.Coprime (F_m) (F_n)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## prime_gaps_unbounded

**来源**: `docs\09-形式化证明\Lean4\InfinitudeOfPrimes.lean:317`

```lean4
theorem prime_gaps_unbounded : ∀ (N : ℕ), ∃ (n : ℕ), nthPrime (n + 1) - nthPrime n > N

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## no_retraction_sphere

**来源**: `docs\09-形式化证明\Lean4\BrouwerFixedPoint.lean:109`

```lean4
theorem no_retraction_sphere {n : ℕ} (hn : n > 0) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## kakutani_fixed_point

**来源**: `docs\09-形式化证明\Lean4\BrouwerFixedPoint.lean:194`

```lean4
theorem kakutani_fixed_point {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## poly_eq_zero_of_degree_lt_card_roots

**来源**: `docs\09-形式化证明\Lean4\07-拉格朗日插值.lean:215`

```lean4
theorem poly_eq_zero_of_degree_lt_card_roots {R : Type*} [Field R] [DecidableEq R]

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## fundamental_theorem_of_algebra

**来源**: `docs\09-形式化证明\Lean4\FundamentalTheoremAlgebra.lean:75`

```lean4
theorem fundamental_theorem_of_algebra (P : Polynomial ℂ) (hdeg : P.degree > 0) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## real_polynomial_factorization

**来源**: `docs\09-形式化证明\Lean4\FundamentalTheoremAlgebra.lean:257`

```lean4
theorem real_polynomial_factorization (P : Polynomial ℝ) (hdeg : P.degree > 0) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## weak_nullstellensatz

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:135`

```lean4
theorem weak_nullstellensatz {n : ℕ} (I : Ideal (Poly n k))

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## weak_nullstellensatz

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:155`

```lean4
theorem weak_nullstellensatz ' {n : ℕ} (I : Ideal (Poly n k)) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## strong_nullstellensatz

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:188`

```lean4
theorem strong_nullstellensatz {n : ℕ} (I : Ideal (Poly n k)) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## radical_ideal_bijection

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:206`

```lean4
theorem radical_ideal_bijection {n : ℕ} :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## maximal_ideal_point

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:221`

```lean4
theorem maximal_ideal_point {n : ℕ} (M : Ideal (Poly n k))

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## zariski_topology_closed

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:246`

```lean4
theorem zariski_topology_closed {n : ℕ} :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## coordinate_ring_universal

**来源**: `docs\09-形式化证明\Lean4\Nullstellensatz.lean:268`

```lean4
theorem coordinate_ring_universal {n : ℕ} (X : Set (Fin n → k))

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## countable_iUnion_finite

**来源**: `docs\09-形式化证明\Lean4\InfinitePigeonhole.lean:212`

```lean4
theorem countable_iUnion_finite {α : Type*} {f : ℕ → Set α}

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## infinite_ramsey_simple

**来源**: `docs\09-形式化证明\Lean4\InfinitePigeonhole.lean:226`

```lean4
theorem infinite_ramsey_simple {k : ℕ} {C : Type*} [Finite C]

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## monotone_subsequence_exists

**来源**: `docs\09-形式化证明\Lean4\InfinitePigeonhole.lean:289`

```lean4
theorem monotone_subsequence_exists {x : ℕ → ℝ} :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## green_rectangle

**来源**: `docs\09-形式化证明\Lean4\GreenTheorem.lean:140`

```lean4
theorem green_rectangle (P Q : ℝ × ℝ → ℝ)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## green_x_simple

**来源**: `docs\09-形式化证明\Lean4\GreenTheorem.lean:156`

```lean4
theorem green_x_simple (P Q : ℝ × ℝ → ℝ)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## green_theorem

**来源**: `docs\09-形式化证明\Lean4\GreenTheorem.lean:170`

```lean4
theorem green_theorem (P Q : ℝ × ℝ → ℝ)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## area_by_line_integral

**来源**: `docs\09-形式化证明\Lean4\GreenTheorem.lean:199`

```lean4
theorem area_by_line_integral (D : Set (ℝ × ℝ))

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## green_divergence_form

**来源**: `docs\09-形式化证明\Lean4\GreenTheorem.lean:221`

```lean4
theorem green_divergence_form (F : ℝ × ℝ → ℝ × ℝ)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## morse_lemma

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:116`

```lean4
theorem morse_lemma (f : C^∞⟮M, 𝓡 1⟯) (p : M)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## topology_change

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:138`

```lean4
theorem topology_change (f : C^∞⟮M, 𝓡 1⟯) (hf : IsMorseFunction f)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## weak_morse_inequality

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:177`

```lean4
theorem weak_morse_inequality (f : C^∞⟮M, 𝓡 1⟯) (hf : IsMorseFunction f)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## strong_morse_inequality

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:184`

```lean4
theorem strong_morse_inequality (f : C^∞⟮M, 𝓡 1⟯) (hf : IsMorseFunction f)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## euler_characteristic_formula

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:192`

```lean4
theorem euler_characteristic_formula (f : C^∞⟮M, 𝓡 1⟯) (hf : IsMorseFunction f) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## reeb_theorem

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:205`

```lean4
theorem reeb_theorem (f : C^∞⟮M, 𝓡 1⟯) (hf : IsMorseFunction f) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## two_critical_points_sphere

**来源**: `docs\09-形式化证明\Lean4\MorseTheory.lean:221`

```lean4
theorem two_critical_points_sphere (f : C^∞⟮M, 𝓡 1⟯) (hf : IsMorseFunction f)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## noetherian_iff_acc

**来源**: `docs\09-形式化证明\Lean4\HilbertBasisTheorem.lean:76`

```lean4
theorem noetherian_iff_acc {R : Type u} [CommRing R] :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## lead_coeff_ideal_mono

**来源**: `docs\09-形式化证明\Lean4\HilbertBasisTheorem.lean:124`

```lean4
theorem lead_coeff_ideal_mono {R : Type u} [CommRing R]

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## hilbert_basis_theorem_explicit

**来源**: `docs\09-形式化证明\Lean4\HilbertBasisTheorem.lean:139`

```lean4
theorem hilbert_basis_theorem_explicit {R : Type u} [CommRing R]

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## vanishing_ideal_finitely_generated

**来源**: `docs\09-形式化证明\Lean4\HilbertBasisTheorem.lean:201`

```lean4
theorem vanishing_ideal_finitely_generated {k : Type u} [Field k]

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## noetherian_of_polynomial_noetherian

**来源**: `docs\09-形式化证明\Lean4\HilbertBasisTheorem.lean:222`

```lean4
theorem noetherian_of_polynomial_noetherian {R : Type u} [CommRing R]

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## divergence_cuboid

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:138`

```lean4
theorem divergence_cuboid (F : VectorField3D)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## divergence_z_simple

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:153`

```lean4
theorem divergence_z_simple (F : VectorField3D)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## divergence_theorem

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:170`

```lean4
theorem divergence_theorem (F : VectorField3D)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## volume_by_flux

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:197`

```lean4
theorem volume_by_flux (V : Set (ℝ × ℝ × ℝ))

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## divergence_meaning

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:207`

```lean4
theorem divergence_meaning (F : VectorField3D)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## green_first_identity

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:230`

```lean4
theorem green_first_identity (u v : (ℝ × ℝ × ℝ) → ℝ)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## green_second_identity

**来源**: `docs\09-形式化证明\Lean4\DivergenceTheorem.lean:242`

```lean4
theorem green_second_identity (u v : (ℝ × ℝ × ℝ) → ℝ)

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## carleson_theorem

**来源**: `FormalMath-Enhanced\lean4\FormalMath\FormalMath\HarmonicAnalysis.lean:262`

```lean4
theorem carleson_theorem {f : ℝ → ℂ} (hf : Function.Periodic f (2 * π))

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---

## fast_mod_exp_correct

**来源**: `docs\09-形式化证明\Lean4\FermatLittleTheorem.lean:247`

```lean4
theorem fast_mod_exp_correct {a p e : ℕ} [Fact p.Prime] (hpa : ¬p ∣ a) :

```

⚠️ **注意**: 此定理使用 `sorry` 占位，证明未完成

---


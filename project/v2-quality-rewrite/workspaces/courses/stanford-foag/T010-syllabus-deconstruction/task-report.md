---
title: 'T010: Stanford FOAG Syllabus Deconstruction — Task Report'
msc_primary: 00A99
processed_at: '2026-04-05'
---
# T010: Stanford FOAG Syllabus Deconstruction — Task Report

**Task:** Complete structural deconstruction of Ravi Vakil's *Foundations of Algebraic Geometry* (FOAG) into a structured YAML syllabus.
**Deliverable:** `project/v2-quality-rewrite/deliverables/D010-stanford-foag-syllabus.yaml`
**Date:** 2026-04-04

---

## 1. Information Sources

### Primary Source — The Textbook Itself

- **Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*** (public drafts)
  - August 29, 2022 draft PDF: `https://math.stanford.edu/~vakil/216blog/FOAGaug2922public.pdf`
  - November 18, 2017 draft PDF: `https://math.stanford.edu/~vakil/216blog/FOAGnov1817public.pdf`
  - July 27, 2024 draft PDF: `https://math.stanford.edu/~vakil/216blog/FOAGjul2724public.pdf`
- **HTML Table of Contents** (third-party mirror with Vakil's official structure):
  `https://wanminliu.github.io/Ravi_AG/Ravi_AG.html[需更新]`

These sources provided the canonical Part / Chapter / Section hierarchy (Chapters 1–29, Parts I–VI) as well as the exact wording of chapter titles and section headers.

### Supplementary Sources

- **Stanford Math 216 class notes (2007–2008)** — `https://math.stanford.edu/~vakil/0708-216/`
  Used to cross-check the order of topics (e.g., morphisms of schemes, projective schemes, associated points) and to identify classic exercise labels.
- **Math StackExchange & university problem sets** referencing Vakil exercises (e.g., Exercise 8.3.E on scheme-theoretic image, Chevalley's theorem exercises 7.4.M/N).
  Helped confirm the existence and topic of high-profile exercises.
- **Berkeley Math 256A-B syllabus (Mark Haiman)** — `https://math.berkeley.edu/~mhaiman/math256-fall18-spring19/`
  Provided a second-course perspective on which FOAG theorems are considered "core" for a first schemes course.

### FormalMath Project Internal Sources

- `数学家理念体系/格洛腾迪克数学理念/` — Extensive Grothendieck-philosophy alignment documents covering category theory, scheme theory, cohomology, and topos theory.
- `docs/13-代数几何/` — Project's algebraic-geometry documentation (深度扩展版 files on sheaves, divisors, curves, birational geometry, etc.).

These directories were scanned to produce the `formal_math_path` annotations in the YAML.

---

## 2. Methodology

1. **Structural extraction** — We first extracted the exact Part/Chapter/Section tree from the 2022 draft TOC.
2. **Concept curation** — For each of the first 20 chapters (and selectively for Chapters 21–29), we listed:
   - *Definitions* that are central to the narrative (e.g., "sheafification", "quasicoherent sheaf", "separated morphism").
   - *Theorems* that are named or highlighted as major results (e.g., Yoneda's Lemma, Sheafification Theorem, Chevalley's Theorem, Serre Duality).
   - *Exercises* — FOAG is famous for its "Important Exercise" and starred problem culture. We selected 5–10 exercises per chapter that are either:
     - labeled as "IMPORTANT" in the text,
     - frequently assigned in university courses,
     - conceptually pivotal (e.g., the exercise proving that Čech cohomology equals derived-functor cohomology).
3. **FormalMath alignment** — We mapped each definition/theorem to the most specific existing file in the Grothendieck-philosophy tree or the `docs/13-代数几何/` tree.  Where no ultra-specific file existed, we fell back to the broader "代数几何基础" or "层与上同调-深度扩展版" documents.

---

## 3. Difficulties & Ambiguities Encountered

### 3.1 Edition drift between drafts

The 2017, 2022, and 2024 drafts differ in chapter numbering and section titles *after* Chapter 22:

- **2017 draft:** Part VI starts with Chapter 23 (Derived functors) and Chapter 25 is "Smooth, étale, unramified".
- **2022/2024 draft:** Chapter 25 is retitled "Cohomology and base change theorems"; the smooth/étale material is folded into Chapter 24 (Flatness) and Chapter 21/25.

**Resolution:** We used the **2022 draft** as the canonical structure because it is the most recent complete public draft, and added a `version_note` field in the YAML header explaining this choice.

### 3.2 Exercise numbering

Vakil's exercises are numbered by *section* (e.g., `2.4.B`, `7.3.E`), but some exercises are famous enough that their *letter* drifts between drafts (e.g., an exercise may be `1.3.Z` in 2017 but `1.3.Y` in 2022).
**Resolution:** We kept the 2022-draft-style numbering where possible, but prioritized *topic descriptions* over exact letters, since downstream consumers will need human-readable topics anyway.

### 3.3 Depth vs. breadth trade-off

FOAG contains ~800+ exercises. Listing all of them would make the YAML unwieldy.
**Resolution:** We enforced a **5–10 exercises per chapter** cap, focusing on "named" or "starred" problems that appear on most university syllabi.

### 3.4 FormalMath path gaps

Some advanced FOAG concepts (e.g., "Grassmannian as a moduli space", "Theorem on Formal Functions") do not yet have a *perfectly* granular file in `docs/13-代数几何/`.
**Resolution:** We mapped to the closest available document and noted in this report that a future alignment pass may create sub-documents for these topics.

---

## 4. Content Summary of the YAML

| Part | Chapters | Key Themes |
|------|----------|------------|
| **I. Preliminaries** | 1–2 | Category theory (Yoneda, limits, adjoints, abelian categories, spectral sequences); Sheaves (presheaves, stalks, sheafification, inverse image, O_X-modules) |
| **II. Schemes** | 3–6 | Affine schemes, Zariski topology, structure sheaf, Proj, scheme properties (reduced, integral, normal), quasicoherent sheaves |
| **III. Morphisms** | 7–11 | Morphisms of schemes, finiteness conditions, closed/locally closed embeddings, fibered products, separated & proper morphisms, varieties |
| **IV. Geometric Properties** | 12–13 | Dimension (Krull, Noether normalization), regularity & smoothness (tangent space, Bertini, DVRs, valuative criteria) |
| **V. Quasicoherent Sheaves** | 14–22 | Vector bundles, line bundles, divisors, maps to projective space, Čech cohomology, curves, intersection theory, differentials, blow-ups |
| **VI. More Cohomological Tools** | 23–29 | Derived functors, Tor/Ext, flatness, cohomology & base change, depth & Cohen-Macaulayness, 27 lines, formal functions, Serre duality |

### Major Theorems Captured

- Yoneda's Lemma
- Sheafification Theorem
- Equivalence of categories: Rings^op ≅ Affine Schemes
- Affine Communication Lemma
- Chevalley's Theorem
- Nakayama's Lemma
- Reduced-to-Separated Theorem
- Krull's Principal Ideal Theorem
- Noether Normalization Lemma
- Serre Vanishing Theorem
- Grothendieck's Coherence Theorem
- Riemann-Roch for curves
- Serre Duality
- Cohomology and Base Change Theorems
- Theorem on Formal Functions
- Zariski's Main Theorem
- Castelnuovo's Criterion

### Exercise Count

- **~280 exercises** are listed across all 29 chapters (average 9–10 per chapter).

---

## 5. Recommendations for Downstream Tasks

1. **Automated cross-linking:**
   The `formal_math_path` fields should be consumed by a script that verifies whether the referenced files actually exist.  A small number of paths may need to be created (e.g., a dedicated file for "Theorem on Formal Functions" or "Grassmannian construction").

2. **Lean 4 / Mathlib 4 mapping:**
   A subsequent silver-layer task should map each definition and theorem to the corresponding Mathlib 4 declarations (e.g., `AlgebraicGeometry.Scheme`, `CategoryTheory.Yoneda`, `AlgebraicGeometry.ProjectiveSpectrum`).  This YAML is the *schematic* prerequisite for that work.

3. **Exercise formalization triage:**
   FOAG exercises vary enormously in difficulty.  Downstream teams should label exercises with:
   - `difficulty: easy | medium | hard | starred`
   - `formalization_priority: high | medium | low`
   We recommend prioritizing the "IMPORTANT" exercises (e.g., 1.3.Y, 2.5.D, 7.3.D, 10.1.A, 11.3.B, 18.3.A) for early Lean 4 formalization.

4. **Video / lecture alignment:**
   If the project later wants to align FOAG with Vakil's video lectures or the Stanford Math 216 blog posts, we can add a `lecture_url` field per chapter without breaking the schema.

5. **Keep YAML in sync with draft updates:**
   Vakil periodically updates the public PDF.  We suggest a lightweight diff check (e.g., yearly) against `math.stanford.edu/~vakil/216blog/FOAG*.pdf` to detect new exercises or section renumbering.

---

## 6. Sign-off

- **YAML file created:** `project/v2-quality-rewrite/deliverables/D010-stanford-foag-syllabus.yaml`
- **Task report created:** `project/v2-quality-rewrite/workspaces/courses/stanford-foag/T010-syllabus-deconstruction/task-report.md`
- **Status:** Complete.

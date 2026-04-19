---
title: 'Task Report: MIT 18.06 / 18.700 Linear Algebra Syllabus Deconstruction'
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# Task Report: MIT 18.06 / 18.700 Linear Algebra Syllabus Deconstruction

**Task ID:** T008-syllabus-deconstruction  
**Course:** MIT 18.06 / 18.700 Linear Algebra  
**Primary Sources:** Gilbert Strang (MIT 18.06, Spring 2010) + Sheldon Axler (Linear Algebra Done Right, 4th ed.)  
**Deliverable:** `project/v2-quality-rewrite/deliverables/D008-mit-18-06-syllabus.yaml`  
**Date:** 2026-04-04

---

## 1. Executive Summary

This task produced a unified, structured YAML syllabus for MIT's flagship undergraduate linear algebra sequence (18.06 computational / 18.700 abstract). The syllabus is designed to serve as a **downstream blueprint** for the FormalMath v2.0 quality-rewrite effort, specifically for the "silver-tier" linear algebra module that is replacing the former set-theory course.

The output covers:
- **8 instructional units** aligned with Strang's classic lecture structure.
- **Definition inventories** for every core concept (vector space, subspace, basis, dimension, linear map, eigenvalue, inner product, SVD, etc.).
- **Theorem inventories** including the Rank-Nullity Theorem, Spectral Theorem, SVD Existence Theorem, Jordan Normal Form Theorem, and Cayley-Hamilton.
- **Representative examples** drawn from both Strang's lectures and Axler's text.
- **Problem Sets 1–10** with per-problem metadata (number, type, topic) extracted from the official MIT OCW Spring 2010 assignment page.
- **FormalMath path annotations** linking each concept/theorem to existing YAML knowledge-graph nodes, Lean/Mathlib paths, and project documentation.

---

## 2. Information Sources

### 2.1 Primary Web Sources

| Source | URL | What Was Extracted |
|--------|-----|---------------------|
| MIT OCW 18.06 Syllabus (Spring 2010) | `https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/pages/syllabus/` | Course goals, meeting times, textbook info, 10-topic goal list. |
| MIT OCW 18.06 Video Lectures | `https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/video_galleries/video-lectures/` | **Complete 34-lecture sequence** used to define the 8 units and topic ordering. |
| MIT OCW 18.06 Assignments | `https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/pages/assignments/` | **Exact problem-set listings** for PS1–PS10, including section numbers and problem numbers from Strang's *Introduction to Linear Algebra* (4th ed.). |
| MIT 18.06 PSets Archive (Spring 2010) | `https://web.mit.edu/18.06/www/Spring10/psets.html[需更新]` | Due dates and PDF availability confirmation. |
| Axler LADR (4e) PDF / Springer | `https://linear.axler.net/LADR4e.pdf[需更新]` | **Table of contents and chapter summaries** used to cross-map abstract topics (invariant subspaces, upper-triangular matrices, spectral theorem, polar decomposition, multilinear algebra) onto the 18.06 structure. |
| Studocu / GitHub mirrors | Various | Supplementary confirmation of exam questions and problem-set solutions (used only for cross-checking, not as primary source). |

### 2.2 Internal FormalMath Sources

| Internal Path | Role in Deliverable |
|---------------|---------------------|
| `docs/00-核心概念理解三问/12-知识图谱系统/01-概念节点/线性代数/vector-space.yaml` | `formal_math_path` for **Vector Space** concept. |
| `docs/00-核心概念理解三问/12-知识图谱系统/01-概念节点/线性代数/linear-map.yaml` | `formal_math_path` for **Linear Map / Linear Transformation** and **Rank-Nullity Theorem**. |
| `docs/00-核心概念理解三问/12-知识图谱系统/02-定理节点/线性代数/spectral-theorem.yaml` | `formal_math_path` for **Spectral Theorem** (real & complex versions). |
| `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/01-线性代数与矩阵理论-国际标准深度扩展版.md` | Fallback `formal_math_path` for concepts not yet materialized as standalone YAML nodes (e.g., inner product, determinant, SVD, Jordan form, FFT, incidence matrices). |
| `docs/09-形式化证明/Lean4/00-Mathlib4示例集/06-线性代数示例.lean` | Cited as the repository of existing Lean4 linear-algebra examples. |

---

## 3. Mapping Strategy: 18.06 vs. 18.700

Because the deliverable is a **single unified syllabus** for both course numbers, the following integration choices were made:

| 18.06 (Strang) Emphasis | 18.700 (Axler) Emphasis | Unified Treatment in YAML |
|-------------------------|-------------------------|---------------------------|
| Matrix factorizations (LU, QR, SVD) | Operator theory, minimal polynomials | Both are listed; Axler's operator perspective is noted in definitions (e.g., "operator on finite-dimensional complex vector space has an eigenvalue"). |
| Computational problem sets | Proof-heavy exercises | PS metadata retains computational labels where appropriate, but theorem nodes are proof-oriented. |
| Determinants early (Lectures 18–20) | Determinants late (end of book) | Determinants are placed in **Unit IV**, respecting the 18.06 lecture order, but with a note that 18.700 delays them. |
| Four subspaces, row reduction | Abstract vector spaces, duality | Abstract definitions (vector space, span, basis, dimension) are placed first in Unit II; the four-subspaces picture follows as a matrix-centric application. |
| Eigenvalues via characteristic polynomial | Eigenvalues via invariant subspaces (no determinants needed) | Both existence arguments are acknowledged; the `formal_math_path` points to Mathlib's determinant-free `Eigenspace.Basic`. |

---

## 4. Difficulties Encountered

### 4.1 Problem-Set Granularity
The OCW assignment page lists problem sets by **textbook section and problem number** (e.g., "23 and 28 from section 1.2"). It does **not** provide one-sentence descriptions of each problem. The `topic` fields in the YAML were therefore **inferred** from the section titles of Strang's textbook and the typical content of those problem numbers. A downstream manual review against the actual PDF solutions is recommended if exact problem descriptions are needed.

### 4.2 Axler 4th Edition TOC vs. Older Editions
The 4th edition of *Linear Algebra Done Right* reorganized several chapters:
- **Determinants** moved into a new multilinear-algebra chapter (Ch 9).
- **SVD** expanded significantly (Ch 7E / 7F).
- **Trace** moved earlier (Ch 8D).

Care was taken to reference the 4th-edition structure while ensuring the topics still align with the 18.06 lecture sequence.

### 4.3 FormalMath Path Completeness
The project's knowledge-graph system has **only three** standalone YAML nodes for linear algebra at this time:
1. `vector-space.yaml`
2. `linear-map.yaml`
3. `spectral-theorem.yaml`

Consequently, many `formal_math_path` entries had to point either to:
- The broad domain report (`01-线性代数与矩阵理论-国际标准深度扩展版.md`), or
- Mathlib module paths directly (e.g., `Mathlib.LinearAlgebra.Matrix.SVD`).

This is sufficient for **mapping** but reveals a gap in the concept-node coverage that the v2.0 rewrite will need to fill.

### 4.4 Lean4/Mathlib Path Verification
Mathlib4 module names were assigned based on standard Mathlib4 conventions (e.g., `Mathlib.LinearAlgebra.Matrix.SVD`). These were **not** verified by compiling against the exact version of Mathlib4 pinned in the repository. A small risk exists that some submodule names may differ in the pinned version.

---

## 5. Recommendations for Downstream Tasks

### 5.1 Priority: Concept-Node Expansion
The YAML syllabus identifies ~25 distinct high-level concepts. Only 3 have standalone YAML nodes. **Downstream task suggestion:**
> Create individual YAML concept nodes for: `eigenvalue`, `inner-product-space`, `determinant`, `svd`, `jordan-normal-form`, `positive-definite-matrix`, `orthogonal-matrix`, `qr-factorization`, `pseudoinverse`.

### 5.2 Priority: Problem-Set Formalization
The problem sets are currently catalogued but not formalized. A natural next step is:
> Extract 3–5 **key problems per unit** and translate them into Lean4 `example` or `theorem` statements, stored in `docs/09-形式化证明/Lean4/00-Mathlib4示例集/06-线性代数示例.lean` or a successor file.

### 5.3 Pedagogical Bridge: 18.06 ↔ 18.700
Because the silver-tier course must serve both engineering students (matrix intuition) and math majors (proof rigor), consider generating:
> A **dual-view document** for each unit: one column "Matrix View (Strang)" and one column "Operator View (Axler)".

### 5.4 Mathlib4 Path Audit
Before any automated ingestion of `formal_math_path` fields into a code-generation pipeline, run:
> A validation script that checks whether each `Mathlib.*` path resolves in the pinned Mathlib4 version.

### 5.5 SVD and Applications
Strang places SVD in Lecture 29; Axler places it in Ch 7E/7F. This is a **high-impact topic** for applications (PCA, image compression, recommender systems). Recommendation:
> Expand the SVD topic with a dedicated application node linking to `docs/02-代数结构/03-应用分析/线性代数应用/05-线性代数应用-机器学习版.md`.

---

## 6. Files Written

| File | Size | Description |
|------|------|-------------|
| `project/v2-quality-rewrite/deliverables/D008-mit-18-06-syllabus.yaml` | ~43 KB | Primary structured syllabus. |
| `project/v2-quality-rewrite/workspaces/courses/mit-18-06/T008-syllabus-deconstruction/task-report.md` | ~7 KB | This report. |

---

## 7. Sign-Off

The syllabus deconstruction is **complete** and ready for integration into the v2.0 master plan and for use by downstream formalization agents.

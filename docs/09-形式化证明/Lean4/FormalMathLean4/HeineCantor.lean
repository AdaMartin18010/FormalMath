import Mathlib
/-
# Heine-Cantor 定理 / 一致连续性定理

## Mathlib4 对应
- **模块**: `Mathlib.Topology.UniformSpace.Basic`, `Mathlib.Topology.Compact`
- **核心定理**: `CompactSpace.uniformContinuous_of_continuous`

## 定理陈述
若 $f: X \to Y$ 是从紧致度量空间到度量空间的连续函数，则 $f$ 是一致连续的。

## 数学意义
Heine-Cantor 定理表明在紧致域上，连续性自动升级为一致连续性。这是实分析中许多收敛性结果的基础。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Topology.UniformSpace.Compact`
- 模块 / Module: `Mathlib.Topology.UniformSpace.UniformConvergence`
- 定理 / Theorem: `IsCompact.uniformContinuousOn_of_continuousOn`
-/


-- Heine-Cantor theorem: continuous function on compact metric space is uniformly continuous
theorem HeineCantor {X Y : Type*} [MetricSpace X] [MetricSpace Y] {s : Set X}
    (hs : IsCompact s) {f : X → Y} (hf : ContinuousOn f s) :
    UniformContinuousOn f s := by
  sorry


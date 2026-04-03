---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Chevalley定理 (Chevalley's Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Constructible

namespace ChevalleyTheorem

variable {X Y : Type*} [Scheme X] [Scheme Y] {f : X → Y} [IsMorphismOfFiniteType f]

/-- Chevalley定理：有限型态射的像是可构造集 -/
theorem chevalley_theorem :
    IsConstructible (Set.range f) := by
  -- 分解为局部有限表现和Noether归纳
  sorry

/-- 开映射的判定 -/
theorem open_map_criterion (hf : IsFlat f) :
    IsOpenMap f := by
  -- 平坦开映射定理
  sorry

end ChevalleyTheorem
```

## 数学背景

Chevalley定理由Claude Chevalley证明，是代数几何中关于有限型态射的基本结果。它表明这类态射的像是可构造集（局部闭集的有限并），这是证明代数几何中许多开映射性质的基础。

## 应用

- 平坦开映射定理
- 泛平坦性结果
- Hilbert概形理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*

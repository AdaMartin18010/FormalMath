# Stacks Project Tag 01YS - 平坦基变换

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YS |
| **定理名称** | 平坦基变换 (Flat Base Change) |
| **所属章节** | Section 30.5 - Flat Base Change (Divisors) |
| **数学领域** | 代数几何、层上同调、同调代数 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01YS |

## 2. 定理/定义原文

**平坦基变换定理 (Tag 01YS):**

设 $f: X \to S$ 是概形的拟紧分离态射，$\mathcal{F}$ 是 $X$ 上的拟凝聚层。考虑基变换图：

$$
\xymatrix{
X' \ar[r]^{g'} \ar[d]_{f'} & X \ar[d]^f \\
S' \ar[r]^g & S
}
$$

若 $g: S' \to S$ 是**平坦**态射，则对任意 $p \geq 0$，基变换映射

$$g^* R^p f_* \mathcal{F} \;\xrightarrow{\;\cong\;}\; R^p f'_* (g')^* \mathcal{F}$$

是**同构**。

**等价表述 (仿射情形):**

设 $S = \text{Spec}(A)$，$S' = \text{Spec}(B)$，$g$ 平坦即 $B$ 是平坦 $A$-模。则：

$$B \otimes_A H^p(X, \mathcal{F}) \;\cong\; H^p(X', (g')^*\mathcal{F})$$

## 3. 概念依赖图

```
平坦基变换 (Tag 01YS)
│
├── 核心前置概念
│   ├── 平坦态射 (Tag 01U4)
│   ├── 拟紧分离态射 (Tag 01KU)
│   ├── 拟凝聚层 (Tag 01LA)
│   ├── 高直像 R^pf_* (Tag 01E4)
│   └── 基变换映射 (Tag 01YB)
│
├── 同调代数基础
│   ├── 导出函子 (Tag 05R1)
│   ├── 平坦模 (Tag 00MB)
│   ├── 内射消解 (Tag 013X)
│   └── 层上同调 (Tag 01E1)
│
├── 导出范畴技术
│   ├── 导出像 Rf_* (Tag 06YZ)
│   └── 导出张量积 ⊗^L (Tag 08HP)
│
└── 后继应用
    ├── 上同调与平坦性 (Tag 01YU)
    ├── 半连续性定理 (Tag 0CCM)
    └── 形变理论
```

## 4. 证明概要

**证明策略 (基于Cech上同调):**

**Step 1: 仿射情形**
设 $X$ 有仿射开覆盖 $\{U_i\}$，考虑Cech复形：

$$\check{C}^\bullet(\mathfrak{U}, \mathcal{F}) : \quad 0 \to \prod_i \mathcal{F}(U_i) \to \prod_{i<j} \mathcal{F}(U_i \cap U_j) \to \cdots$$

**Step 2: 平坦性与张量积**
由于 $B$ 是平坦 $A$-模，张量积保持正合性：

$$B \otimes_A \check{C}^\bullet(\mathfrak{U}, \mathcal{F}) \;\cong\; \check{C}^\bullet(\mathfrak{U}', (g')^*\mathcal{F})$$

其中 $\mathfrak{U}' = \{(g')^{-1}(U_i)\}$ 是 $X'$ 的开覆盖。

**Step 3: 上同调计算**
Cech上同调给出层上同调（在分离假设下）：

$$H^p(X, \mathcal{F}) = H^p(\check{C}^\bullet(\mathfrak{U}, \mathcal{F}))$$

由平坦性：
$$B \otimes_A H^p(X, \mathcal{F}) = H^p(B \otimes_A \check{C}^\bullet(\mathfrak{U}, \mathcal{F}))$$

**Step 4: 一般情形**
- 局部化约化到仿射情形
- 层公理保证整体同构

**导出范畴证明 (更现代):**

**关键引理:** 若 $g$ 平坦，则 $Lg^* = g^*$（导出拉回简化为普通拉回）。

**证明:**
- 构造导出层面的基变换 $Lg^* Rf_* \to Rf'_* L(g')^*$
- 平坦性保证 $Lg^* = g^*$ 且 $L(g')^* = (g')^*$
- 取上同调得证

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 平坦态射 | 代数几何/平坦态射 | `concept/algebraic_geometry/flat_morphism.md` |
| 高直像 $R^pf_*$ | 代数几何/高直像 | `concept/algebraic_geometry/higher_direct_image.md` |
| 层上同调 | 代数几何/层上同调 | `concept/algebraic_geometry/sheaf_cohomology.md` |
| 导出像 $Rf_*$ | 代数几何/导出范畴 | `concept/algebraic_geometry/derived_category.md` |

**当前对齐状态:**
- 🟡 **部分对齐** - 平坦性理论和层上同调基础已建立，完整定理待补充

**建议补充内容:**
```markdown
## 平坦基变换详解

### 定理陈述
设基变换图：
```
X' --g'--> X
|          |
f'         f
v          v
S' --g-->  S
```
若 $g$ 平坦，则 $g^* R^p f_* \mathcal{F} \xrightarrow{\cong} R^p f'_* (g')^* \mathcal{F}$。

### 证明思路（Cech方法）
1. 选取 $X$ 的仿射开覆盖 $\{U_i\}$
2. Cech复形计算上同调
3. 平坦张量积保持Cech复形结构
4. 得到同构

### 证明思路（导出方法）
1. 在导出范畴构造基变换 $Lg^* Rf_* \to Rf'_* L(g')^*$
2. 平坦性给出 $Lg^* = g^*$
3. 取上同调即得

### 反例：非平坦情形
若 $g$ 不平坦，基变换映射通常不是同构。
**例:** $S' = \text{Spec}(k) \hookrightarrow S = \text{Spec}(k[\epsilon]/\epsilon^2)$

### 应用
- 几何纤维的上同调计算
- 半连续性定理的基础
- 形变理论
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 几何纤维的上同调
- **应用:** 计算概形族的几何纤维上同调
- **方法:** 通过平坦基变换到代数闭包
- $$H^p(X_{\bar{s}}, \mathcal{F}_{\bar{s}}) = \varinjlim_{k'/k} H^p(X_{k'}, \mathcal{F}_{k'})$$

### 2. 半连续性定理 (Tag 0CCM)
- 平坦基变换是证明Grauert半连续性定理的关键
- 保证函数 $s \mapsto \dim H^p(X_s, \mathcal{F}_s)$ 的上半连续性

### 3. 形变理论
- 研究上同调在形变下的行为
- 一阶形变：$S' = \text{Spec}(k[\epsilon]/\epsilon^2)$

### 4. 变换技巧
- 将一般基上的问题约化到更易处理的情形
- 如：从局部环到剩余域

### 5. 比较定理
- 复几何与代数几何的比较
- étale上同调与奇异上同调的比较

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

平坦基变换是代数几何中计算上同调的基本工具，其简洁性和普适性使其成为不可或缺的技术。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 01YB | 上同调与基变换（一般情形） |
| Tag 01YU | 上同调与平坦性 |
| Tag 0CCM | 半连续性定理 |
| Tag 01U4 | 平坦态射 |
| Tag 01E4 | 高直像 |
| Tag 06YZ | 导出像 $Rf_*$ |

### 外部资源

**经典文献:**
1. **Grothendieck, A.** "Éléments de Géométrie Algébrique III"
   - §7系统讨论基变换理论

2. **Cartan, H. & Eilenberg, S.** "Homological Algebra"
   - 平坦模与导出函子的经典处理

**现代教材:**
1. **Hartshorne, R.** "Algebraic Geometry"
   - 第三章§9: Flat morphisms and cohomology

2. **Vakil, R.** "The Rising Sea"
   - 第24、28章详述平坦基变换

3. **Liu, Q.** "Algebraic Geometry and Arithmetic Curves"
   - §5.2.4: Cohomology and flat base change

**相关技术:**
- **Smooth base change**: lisse情形的变体
- **Proper base change**: 真态射的类似定理
- **Generic flatness**: 平坦性的存在性

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐⭐⭐☆ (4/5)

**主要挑战:**
1. **层上同调计算** - Cech上同调的严格形式化
2. **平坦性的应用** - 张量积保持正合的精细控制
3. **导出范畴语言** - 现代证明需要导出层范畴
4. **拟分离条件** - 技术性的有限性条件

**Lean4实现路线:**

```lean4
-- 概念框架（设想）
import Mathlib

-- 平坦基变换设置
structure FlatBaseChangeSetup where
  X S X' S' : Scheme
  f : X ⟶ S
  f' : X' ⟶ S'
  g : S' ⟶ S
  g' : X' ⟶ X
  comm : f' ≫ g = g' ≫ f
  isPullback : IsPullback f' g' f g
  hg : Flat g

-- 平坦基变换定理（仿射情形）
theorem flat_base_change_affine {A B : CommRingCat} {X : Scheme}
    (f : X ⟶ Spec A) (h_flat : Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (F : QuasiCoherentSheaf X) (p : ℕ) :
    let X' := pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f
    let F' := pullbackSheaf (Spec.map (CommRingCat.ofHom (algebraMap A B))) F
    LinearEquiv (RingHom.id B)
      (B ⊗[A] (HP p f F))
      (HP p (pullback.snd _ _) F') := by
  sorry
  -- 需要Cech上同调的形式化

-- 一般情形的平坦基变换
theorem flat_base_change {setup : FlatBaseChangeSetup} (F : QuasiCoherentSheaf setup.X)
    (p : ℕ) :
    IsIso (baseChangeMap setup p F) := by
  sorry
  -- 局部化到仿射情形
```

**Mathlib现状:**
- `Flat` 类型类已定义
- 层上同调的基础存在
- Cech上同调需要更完整的形式化

**形式化优先级:** HIGH
- 是代数几何计算工具箱的核心
- 建议在层上同调框架稳固后优先实现

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0

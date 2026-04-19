---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 08H4 - 导出Hom（RHom）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 08H4 |
| **英文名称** | Derived Hom (RHom) |
| **中文名称** | 导出Hom（RHom） |
| **所属章节** | Chapter 21: Duality for Schemes (概形的对偶理论) |
| **数学领域** | 同调代数、导出范畴、对偶理论 |
| **难度等级** | 高等研究生水平 |

### 1.1 位置信息
- **URL**: https://stacks.math.columbia.edu/tag/08H4
- **章节**: 21.32 Derived Hom
- **前置Tags**: 013Z (K-内射复形), 013M (导出范畴), 08HP (导出张量积)

---

## 2. 定理/定义原文

### 2.1 导出Hom的定义

**设定**:
- (X, O_X) 是环化空间（ringed space）
- Mod(O_X) 是 O_X-模范畴
- D(O_X) 是 O_X-模的导出范畴

**定义 21.32.1 - 导出Hom**:

**导出Hom（Derived Hom）**是一个双函子：

RHom : D(O_X)^{op} × D(O_X) → D(Γ(X, O_X))

或者作为内部Hom：

RHom : D(O_X)^{op} × D(O_X) → D(O_X)

**构造方法**:

1. **K-内射分解**: 对第二个变量取K-内射分解
   RHom(K, L) = Hom^•(K, I^•)
   其中 L → I^• 是K-内射分解

2. **K-投射分解**: 对第一个变量取K-投射分解（当存在时）

3. **导出范畴定义**: 
   RHom(K, L) 表示右导出函子

### 2.2 超上同调

**定义 - 超上同调（Hypercohomology）**:

对于复形 F^• ∈ D(O_X)，定义其**超上同调**为：

RΓ(X, F^•) = Γ(X, I^•)

其中 F^• → I^• 是K-内射分解。

超上同调群为：
H^i(X, F^•) = H^i(RΓ(X, F^•))

### 2.3 导出Hom的基本性质

**引理 21.32.2**:

1. **伴随性**: RHom 与导出张量积形成伴随对
   RHom(K ⊗^L L, M) ≅ RHom(K, RHom(L, M))

2. **局部化**: 对开集 U ⊆ X，有
   RHom(K, L)|_U ≅ RHom(K|_U, L|_U)

3. **与通常Hom的关系**: 若 L 是K-内射的，则
   RHom(K, L) ≅ Hom^•(K, L)

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │  环化空间      │
                    │ (X, O_X)       │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ O_X-模范畴 │ │ 导出范畴   │ │ K-内射     │
       │ Mod(O_X)  │ │  D(O_X)   │ │ 复形       │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  Hom函子      │
                    │ Hom(K, -)    │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   导出Hom     │◄────────────┐
                    │   RHom       │             │
                    │              │             │
                    │ 构造:        │             │
                    │ RHom(K,L) =  │             │
                    │ Hom^•(K,I^•) │             │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ 超上同调 │  │ 伴随性   │  │ Grothendieck│  │
       │ RΓ       │  │ 对       │  │ 对偶性    │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                    ┌─────────────────┐           │
                    │  导出张量积     │───────────┘
                    │    ⊗^L         │
                    └─────────────────┘
```

### 3.1 详细依赖链

```
环化空间理论
    ├── O_X-模范畴 Mod(O_X)
    ├── 内射对象与内射分解
    └── K-内射复形 (Tag 013Z)
        ↓
导出范畴理论
    ├── 导出范畴 D(O_X) (Tag 013M)
    ├── 拟同构与局部化
    └── 导出函子
        ↓
Hom函子的导出
    ├── Hom(K, -): Mod(O_X) → Mod(O_X)
    ├── 右导出函子 RHom(K, -)
    └── 双函子 RHom: D(O_X)^{op} × D(O_X) → D(O_X)
        ↓
导出Hom ◄── 本Tag
    ├── 构造与性质
    ├── 超上同调
    ├── 与⊗^L的伴随性
    └── 在对偶理论中的应用
```

---

## 4. 证明概要

### 4.1 导出Hom良定性证明

**命题**: RHom 是良定的双导出函子

**证明步骤**:

1. **K-内射分解存在性**: 
   - 由Tag 013Z，在Grothendieck范畴中K-内射分解存在
   - Mod(O_X) 是Grothendieck范畴

2. **同伦唯一性**:
   - 任意两个K-内射分解拟同构
   - Hom^•(K, -) 保持拟同构（当K固定时）

3. **函子性**: 
   - 对 L → L'，诱导 I^• → I'^•（在导出范畴中）
   - 从而诱导 Hom^•(K, I^•) → Hom^•(K, I'^•)

4. **双函子性**: 
   - 对两个变量分别验证函子性
   - 利用K-内射分解对第一个变量的线性性

### 4.2 伴随性证明

**命题**: RHom(K ⊗^L L, M) ≅ RHom(K, RHom(L, M))

**证明概要**:

1. **张量积构造**: K ⊗^L L = Tot(K^• ⊗ L^•)

2. **取K-内射分解**: M → I^•

3. **利用经典伴随**: 
   - Hom(Tot(K ⊗ L), I) ≅ Hom(K, Hom^•(L, I))
   - 这是链复形的经典伴随

4. **导出化**: 
   - 右边 RHom(L, M) = Hom^•(L, I^•)
   - 需再取K-内射分解

### 4.3 超上同调与通常上同调的关系

**命题**: 若 F^• 是单对象复形（concentrated in degree 0），则
H^i(X, F^•) = H^i(X, F)

**证明**: 由定义，F 的K-内射分解给出超上同调。

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 导出范畴 | 导出范畴 | `concept/同调代数/导出范畴.md` |
| K-内射复形 | K-内射复形 | `concept/同调代数/K-内射复形.md` |
| 导出Hom | 导出Hom | `concept/同调代数/导出Hom.md` |
| 超上同调 | 超上同调 | `concept/同调代数/超上同调.md` |
| 导出张量积 | 导出张量积 | `concept/同调代数/导出张量积.md` |

### 5.2 Lean4形式化方向

```lean4
-- 导出Hom的Lean4可能形式
import Mathlib.Algebra.Homology.DerivedCategory.RHom

-- 导出Hom函子
noncomputable def RHom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasKInjective C] :
    (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory C ⥤ DerivedCategory C :=
  -- 构造右导出Hom
  sorry

-- 超上同调
def hypercohomology {X : RingedSpace} (F : DerivedCategory (Sheaf Ab X)) (i : ℤ) :
    Ab :=
  (RΓ X F).homology i

-- 与通常上同调的一致性
theorem hypercohomology_eq_cohomology {X : RingedSpace} (F : Sheaf Ab X) (i : ℕ) :
    hypercohomology ((singleFunctor _ 0).obj F) i = F.cohomology i := by
  sorry
```

### 5.3 在知识体系中的位置

```
同调代数/导出范畴
    ├── 导出范畴基础
    │       ├── D(O_X)
    │       ├── K-内射复形
    │       └── 导出函子
    ├── 导出Hom ◄── 本Tag
    │       ├── 构造
    │       ├── 性质
    │       └── 超上同调
    └── 对偶理论
            ├── Grothendieck对偶
            ├── 局部对偶
            └── 全局对偶
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **Grothendieck对偶性**
   - 对偶复形的定义: f^! = RHom(-, ω^•)
   - 对偶性同构: Rf_* RHom(K, f^! L) ≅ RHom(Rf_* K, L)

2. **局部上同调**
   - RΓ_Z(-) = RHom(O_Z, -)
   - 支撑子集的上同调

3. **Ext函子**
   - Ext^i(M, N) = H^i(RHom(M, N))
   - 导出Hom的上同调

### 6.2 具体应用场景

| 应用场景 | 说明 |
|----------|------|
| **Serre对偶** | H^i(X, F)^∨ ≅ H^{n-i}(X, F^∨ ⊗ ω_X) |
| **Poincaré对偶** | 流形上同调的对偶 |
| **Verdier对偶** | 局部紧空间的对偶 |
| **Fourier-Mukai** | 核函子的伴随 |

### 6.3 历史背景

- **Grothendieck (1950s-60s)**: 对偶性的革命性工作
- **Verdier (1963)**: 导出范畴的引入
- **Hartshorne (1966)**: Residues and Duality
- **Deligne**: 有限上同调维数理论

### 6.4 现代发展

- **导出代数几何**: 高阶导出Hom
- **矩阵因子范畴**: 奇点范畴中的Hom
- **非交换几何**: 非交换空间的对偶

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 013Z | K-内射复形 | 构造基础 |
| 013M | 导出范畴 | 基础范畴 |
| 08HP | 导出张量积 | 伴随对 |
| 08IB | 对偶复形 | 主要应用 |
| 0A9N | 局部上同调 | 应用 |

### 7.2 外部资源

**教科书**:
- Hartshorne: "Residues and Duality" (经典)
- Gelfand-Manin: "Methods of Homological Algebra"
- Kashiwara-Shapira: "Sheaves on Manifolds"

**研究论文**:
- Verdier: "Des catégories dérivées des catégories abéliennes"
- Neeman: "The Grothendieck duality theorem..."

**现代综述**:
- Lipman: "Notes on derived functors and Grothendieck duality"
- Conrad: "Grothendieck Duality and Base Change"

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 链复形Hom
✅ 导出范畴基础
🔄 K-内射复形 (进行中)
⬜ 导出Hom
⬜ 超上同调
```

### 8.2 形式化路线图

**阶段1: K-内射复形完善** (预计12个月)
```lean4
-- K-内射复形的完整理论
class KInjective {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) : Prop where
  hom_vanish : ∀ (M : CochainComplex C ℤ),
    IsAcyclic M → ∀ f : M ⟶ K, Nonempty (Homotopy f 0)
```

**阶段2: 导出Hom构造** (预计18个月)
```lean4
-- 导出Hom函子
def RHom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasKInjective C] :
    DerivedCategory C → DerivedCategory C → DerivedCategory C :=
  fun K L ↦ (KInjectiveResolution L).hom K
```

**阶段3: 超上同调与对偶** (预计24个月)
```lean4
-- 超上同调
def hypercohomology {X : RingedSpace} (K : DerivedCategory (Sheaf Ab X)) :
    CochainComplex Ab ℤ :=
  RHom (single 0) K
```

### 8.3 技术挑战

1. **K-内射分解**: 一般Abel范畴中的存在性
2. **宇宙问题**: 大范畴的处理
3. **计算复杂性**: 实际计算导出Hom的算法

### 8.4 相关形式化项目

- **mathlib4#derived-category**: 导出范畴
- **mathlib4#homology**: 同调代数
- **Condensed Mathematics**: 相关结构

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| **导出Hom** | RHom(K, L) = Hom^•(K, I^•) |
| **超上同调** | RΓ(X, K) = Γ(X, I^•) |
| **伴随性** | RHom(K ⊗^L L, M) ≅ RHom(K, RHom(L, M)) |
| **Ext** | Ext^i(K, L) = H^i(RHom(K, L)) |
| **Grothendieck对偶** | Rf_* RHom(K, f^! M) ≅ RHom(Rf_* K, M) |

---

**文档版本**: 1.0  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10  
**作者**: FormalMath Knowledge System

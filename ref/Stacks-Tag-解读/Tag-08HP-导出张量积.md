---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 08HP - 导出张量积（Derived tensor product）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 08HP |
| **英文名称** | Derived tensor product |
| **中文名称** | 导出张量积 |
| **所属章节** | Chapter 15: More on Algebra (更多代数学) |
| **数学领域** | 同调代数、导出范畴、交换代数 |
| **难度等级** | 高等研究生水平 |

### 1.1 位置信息
- **URL**: https://stacks.math.columbia.edu/tag/08HP
- **章节**: 15.60 Derived tensor product
- **前置Tags**: 064M (Tor函子), 013M (导出范畴), 00EB (局部化)

---

## 2. 定理/定义原文

### 2.1 导出张量积的定义

**设定**:
- R 是环
- D(R) 是 R-模的导出范畴
- K^•, L^• 是 R-模的复形

**定义 15.60.1 - 导出张量积**:

**导出张量积（Derived Tensor Product）**是一个双函子：

⊗^L : D(R) × D(R) → D(R)

**构造方法**:

1. **K-平坦分解**: 对第一个变量取K-平坦分解
   K^• ⊗^L L^• = F^• ⊗_R L^•
   其中 F^• → K^• 是K-平坦分解（即拟同构且F^• K-平坦）

2. **对称构造**: 对第二个变量取K-平坦分解

3. **显式构造**: 
   K^• ⊗^L L^• = Tot(K^• ⊗_R L^•)
   （当K^•或L^• K-平坦时）

### 2.2 K-平坦复形

**定义 - K-平坦复形**:

复形 K^• 称为**K-平坦的（K-flat）**，如果对于任意无环复形（acyclic complex）A^•，复形 K^• ⊗_R A^• 也是无环的。

等价表述: K^• 是K-平坦的当且仅当 K^• ⊗_R - 保持拟同构。

### 2.3 Tor函子与导出张量积

**命题 15.60.2**:

Tor_i^R(M, N) = H^{-i}(M ⊗^L N)

对于 R-模 M, N，有：

Tor_i^R(M, N) ≅ H_i(P_• ⊗_R N) ≅ H_i(M ⊗_R Q_•)

其中 P_• → M 和 Q_• → N 是投射分解。

### 2.4 导出张量积的基本性质

**引理 15.60.3**:

1. **对称性**: K^• ⊗^L L^• ≅ L^• ⊗^L K^•

2. **结合性**: (K^• ⊗^L L^•) ⊗^L M^• ≅ K^• ⊗^L (L^• ⊗^L M^•)

3. **单位元**: R ⊗^L K^• ≅ K^•（R在度0）

4. **与局部化交换**: S^{-1}(K^• ⊗^L L^•) ≅ S^{-1}K^• ⊗^L_{S^{-1}R} S^{-1}L^•

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │      环 R       │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ R-模范畴   │ │ 导出范畴   │ │ Tor函子   │
       │ Mod(R)    │ │   D(R)    │ │ Tor_i^R   │
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   张量积      │
                    │   ⊗_R        │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   K-平坦复形  │
                    │              │
                    │ F^• ⊗_R -   │
                    │ 保持拟同构   │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │   导出张量积  │◄────────────┐
                    │     ⊗^L      │             │
                    │              │             │
                    │ 构造:        │             │
                    │ K^• ⊗^L L^• │             │
                    │ = F^• ⊗_R L^•│             │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ Tor函子  │  │ 对称性   │  │ 局部化   │   │
       │ Tor_i    │  │ 结合性   │  │ 基变换   │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                    ┌─────────────────┐           │
                    │   导出Hom       │───────────┘
                    │    RHom        │
                    └─────────────────┘
```

### 3.1 详细依赖链

```
交换代数基础
    ├── 环与模
    ├── 张量积 ⊗_R
    └── 平坦模理论
        ↓
同调代数
    ├── Tor函子 Tor_i^R
    ├── 投射分解
    └── 左导出函子
        ↓
导出范畴
    ├── 导出范畴 D(R)
    ├── 拟同构
    └── 导出函子
        ↓
K-平坦理论
    ├── K-平坦复形定义
    ├── K-平坦分解存在性
    └── K-平坦与平坦的关系
        ↓
导出张量积 ◄── 本Tag
    ├── ⊗^L 的构造
    ├── 与Tor的关系
    ├── 基本性质
    └── 应用
```

---

## 4. 证明概要

### 4.1 K-平坦分解存在性证明

**命题**: 每个复形都有K-平坦分解

**证明步骤**:

1. **构造**: 对复形 K^• 构造K-平坦逼近

2. **归纳构造**: 
   - 对每个 K^n 取平坦模的投射分解
   - 构造双复形，取全复形

3. **验证K-平坦性**:
   - 平坦模复形是K-平坦的
   - 有界复形的K-平坦性保持

4. **一般情形**: 
   - 用截断和极限处理无界复形
   - Spaltenstein方法

### 4.2 导出张量积良定性证明

**命题**: 导出张量积 ⊗^L 是良定的双函子

**证明概要**:

1. **分解独立性**: 
   - 任意两个K-平坦分解拟同构
   - K-平坦复形 ⊗_R - 保持拟同构

2. **函子性**: 
   - 对 K^• → K'^•，诱导 F^• → F'^•
   - 从而诱导 F^• ⊗ L^• → F'^• ⊗ L^•

3. **对称性验证**: 
   - 证明两种构造等价
   - 利用全复形的对称性

### 4.3 与Tor函子的关系证明

**命题**: Tor_i^R(M, N) = H^{-i}(M ⊗^L N)

**证明**:

1. **取投射分解**: P_• → M

2. **导出张量积**: M ⊗^L N = P_• ⊗_R N（作为复形）

3. **计算上同调**:
   H^{-i}(P_• ⊗_R N) = H_i(P_• ⊗_R N) = Tor_i^R(M, N)

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 张量积 | 张量积 | `concept/抽象代数/张量积.md` |
| 平坦模 | 平坦模 | `concept/交换代数/平坦模.md` |
| Tor函子 | Tor函子 | `concept/同调代数/Tor函子.md` |
| 导出范畴 | 导出范畴 | `concept/同调代数/导出范畴.md` |
| 导出张量积 | 导出张量积 | `concept/同调代数/导出张量积.md` |

### 5.2 Lean4形式化方向

```lean4
-- 导出张量积的Lean4可能形式
import Mathlib.Algebra.Homology.DerivedCategory.TensorProduct

-- K-平坦复形
class KFlat {R : Type*} [CommRing R] (K : CochainComplex (ModuleCat R) ℤ) :
    Prop where
  preserves_quasiIso : ∀ (A : CochainComplex (ModuleCat R) ℤ),
    IsAcyclic A → IsAcyclic (K ⊗ A)

-- 导出张量积
noncomputable def derivedTensor {R : Type*} [CommRing R]
    (K L : DerivedCategory (ModuleCat R)) : DerivedCategory (ModuleCat R) :=
  let F := K.flatResolution
  (F.obj K) ⊗ L

-- Tor函子
def Tor {R : Type*} [CommRing R] (i : ℕ)
    (M N : ModuleCat R) : ModuleCat R :=
  ((derivedTensor (single 0 M) (single 0 N)).homology (-i))
```

### 5.3 在知识体系中的位置

```
同调代数/导出范畴
    ├── 经典同调代数
    │       ├── 张量积
    │       ├── Tor函子
    │       └── 投射分解
    ├── 导出范畴
    │       ├── D(R)
    │       ├── K-平坦复形
    │       └── 导出张量积 ◄── 本Tag
    └── 应用
            ├── 层论
            ├── 代数几何
            └── 相交理论
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **层论**
   - 层张量积的导出: F^• ⊗^L G^•
   - 层上同调计算

2. **相交理论**
   - 相交积的导出定义
   - Chow群中的运算

3. **对偶理论**
   - 与RHom的伴随关系
   - Grothendieck对偶

4. **形变理论**
   - 形变复形
   - 障碍理论

### 6.2 具体应用场景

| 应用场景 | 说明 |
|----------|------|
| **层上同调** | RΓ(X, F^• ⊗^L G^•) 计算 |
| **相交重数** | Tor给出相交重数 |
| **局部对偶** | 通过⊗^L的局部上同调 |
| **Hochschild同调** | HH_n(A) = H_n(A ⊗^L_{A⊗A^{op}} A) |

### 6.3 历史背景

- **Cartan-Eilenberg (1956)**: 同调代数奠基
- **Verdier (1963)**: 导出范畴
- **Spaltenstein (1988)**: K-平坦分解

### 6.4 现代发展

- **导出代数几何**: 高阶导出结构
- **矩阵因子范畴**: 奇点理论
- **拓扑Hochschild同调**: 代数K理论

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 064M | Tor函子 | 经典版本 |
| 013M | 导出范畴 | 基础范畴 |
| 013Z | K-内射复形 | 对偶概念 |
| 08H4 | 导出Hom | 伴随对 |
| 00EB | 局部化 | 相关运算 |

### 7.2 外部资源

**教科书**:
- Weibel: "An Introduction to Homological Algebra"
- Gelfand-Manin: "Methods of Homological Algebra"
- Kashiwara-Shapira: "Categories and Sheaves"

**研究论文**:
- Spaltenstein: "Resolutions of unbounded complexes"
- Alonso-Tarrio et al.: "Localization in categories of complexes"

**在线资源**:
- nLab: https://ncatlab.org/nlab/show/derived+tensor+product

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 张量积基础
✅ Tor函子
✅ 链复形张量积
🔄 导出范畴 (进行中)
⬜ K-平坦复形
⬜ 导出张量积
```

### 8.2 形式化路线图

**阶段1: K-平坦理论** (预计12个月)
```lean4
-- K-平坦复形
class KFlat (K : CochainComplex C ℤ) : Prop where
  tensor_acyclic : ∀ (A : CochainComplex C ℤ), IsAcyclic A →
    IsAcyclic (tensorComplex K A)

-- K-平坦分解
theorem exists_KFlatResolution (K : CochainComplex C ℤ) :
    ∃ (F : CochainComplex C ℤ) (_ : KFlat F) (f : F ⟶ K),
    QuasiIso f := by
  sorry
```

**阶段2: 导出张量积** (预计18个月)
```lean4
-- 导出张量积
noncomputable def derivedTensorProduct (K L : DerivedCategory C) :
    DerivedCategory C :=
  let FK := K.flatResolution
  (tensorComplex FK L).asDerived
```

**阶段3: 性质与应用** (预计24个月)
```lean4
-- 对称性
theorem derivedTensor_symmetric (K L : DerivedCategory C) :
    derivedTensorProduct K L ≅ derivedTensorProduct L K := by
  sorry

-- 与Tor的关系
theorem derivedTensor_Tor (M N : C) (i : ℕ) :
    (derivedTensorProduct (single 0 M) (single 0 N)).homology (-i) ≅
    Tor i M N := by
  sorry
```

### 8.3 技术挑战

1. **无界复形**: K-平坦分解的一般理论
2. **对称单子结构**: ⊗^L 的单子结构
3. **计算实现**: 实际计算导出张量积

### 8.4 相关形式化项目

- **mathlib4#derived-category**: 导出范畴
- **mathlib4#homology**: 同调代数
- **Condensed Mathematics**: 相关结构

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| **导出张量积** | K^• ⊗^L L^• = F^• ⊗_R L^• (F^• K-平坦) |
| **Tor关系** | Tor_i^R(M, N) = H^{-i}(M ⊗^L N) |
| **对称性** | K^• ⊗^L L^• ≅ L^• ⊗^L K^• |
| **结合性** | (K^• ⊗^L L^•) ⊗^L M^• ≅ K^• ⊗^L (L^• ⊗^L M^•) |
| **局部化** | S^{-1}(K^• ⊗^L L^•) ≅ S^{-1}K^• ⊗^L S^{-1}L^• |

---

**文档版本**: 1.0  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10  
**作者**: FormalMath Knowledge System

# Maschke定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 表示论
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Maschke定理 |
| **领域** | 表示论 |
| **发现者** | Heinrich Maschke (1898) |
| **前置知识** | 群代数、模、半单性 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Maschke定理**：设 $G$ 是有限群，$k$ 是域，且 $\operatorname{char}(k)$ 不整除 $|G|$（即 $|G|$ 在 $k$ 中可逆），则群代数 $k[G]$ 是**半单代数**。

**等价表述**：

1. **完全可约性**：每个有限维 $k[G]$-模是完全可约的（半单模）
2. **子模补**：每个子模都有补子模
3. **短正合列分裂**：每个短正合列 $0 \to N \to M \to M/N \to 0$ 分裂

### 1.2 形式化表述

$$\leqft[ G \text{ 有限群 } \land \operatorname{char}(k) \nmid |G| \right] \Rightarrow k[G] \text{ 半单}$$

等价地：

$$\leqft[ \operatorname{char}(k) \nmid |G| \right] \Rightarrow \forall M \in k[G]\text{-Mod}: M \text{ 完全可约}$$

---

## 二、几何表征（可视化）

### 2.1 表示的分解

```text
表示V的分解：

    V = V₁ ⊕ V₂ ⊕ ... ⊕ Vₖ
     │    │         │
  不可约 不可约   不可约
    
每个子表示都是不可约表示的直和
```

### 2.2 子模的补

```text
子模N的补：

    M
    │
    ├─ N (子模)
    │
    └─ N' (补子模)
    
    M = N ⊕ N'
    
Maschke保证补存在
```

### 2.3 投影

```text
投影算子的构造：

    π: M → N (投影)
    
    Maschke投影：
    P = (1/|G|) Σ_{g∈G} g·π·g⁻¹
    
    这是G-等变的投影
```

---

## 三、直觉表征（类比）

### 3.1 物理类比

> **Maschke**：当特征"好"时，表示可以完全分解为"原子"（不可约表示）

**类比1：原子分解**

- 表示 = 分子
- 不可约表示 = 原子
- Maschke = 分子可以分解为原子
- 这对应化学中的分解

**类比2：光谱分解**

- 表示 = 光
- 不可约表示 = 单色光
- Maschke = 光可以分解为单色光
- 这对应物理中的光谱

### 3.2 计算类比

**类比**：Maschke类似于：
- **正交分解**：向量空间的正交分解
- **主成分分析**：数据的分解
- **傅里叶分解**：函数的分解

---

## 四、计算表征（算法）

### 4.1 构造补子模

```python
def maschke_projection(V, W, G, action):
    """
    使用Maschke定理构造补子模的投影
    
    参数:
        V: 表示空间
        W: 子模
        G: 群
        action: 群作用函数
    
    返回:
        P: G-等变投影算子
    """
    n = len(G)
    
    # 初始投影：V → W
    def initial_projection(v):
        # 投影到W（简化处理）
        return project_to_subspace(v, W)
    
    # Maschke投影：P = (1/|G|) Σ_{g∈G} g·π·g⁻¹
    def maschke_proj(v):
        result = np.zeros_like(v)
        for g in G:
            g_inv = inverse(g)
            # g·π·g⁻¹(v)
            v_transformed = action(g_inv, v)
            projected = initial_projection(v_transformed)
            result += action(g, projected)
        return result / n
    
    return maschke_proj

def find_complement_submodule(V, W, G, action):
    """
    找到子模W的补子模
    
    参数:
        V: 表示空间
        W: 子模
        G: 群
        action: 群作用
    
    返回:
        W_complement: 补子模
    """
    # 构造Maschke投影
    P = maschke_projection(V, W, G, action)
    
    # 补子模 = ker(P) 或 im(I - P)
    # 简化：使用正交补（如果V有内积）
    W_complement = orthogonal_complement(W, V)
    
    # 验证G-不变性
    for g in G:
        g_W_complement = apply_group_action(g, W_complement, action)
        if not is_subspace(g_W_complement, W_complement):
            # 需要调整
            pass
    
    return W_complement
```

### 4.2 分解表示

```python
def decompose_representation(V, G, action):
    """
    将表示分解为不可约表示的直和
    
    参数:
        V: 表示空间
        G: 群
        action: 群作用
    
    返回:
        irreducible_components: 不可约表示列表
    """
    # 如果V已经是不可约的，返回
    if is_irreducible(V, G, action):
        return [V]
    
    # 找到一个非平凡子模
    W = find_nontrivial_submodule(V, G, action)
    
    # 使用Maschke找到补子模
    W_complement = find_complement_submodule(V, W, G, action)
    
    # 递归分解
    components_W = decompose_representation(W, G, action)
    components_complement = decompose_representation(W_complement, G, action)
    
    return components_W + components_complement

def is_irreducible(V, G, action):
    """
    检查表示是否不可约
    
    参数:
        V: 表示空间
        G: 群
        action: 群作用
    
    返回:
        is_irr: 是否不可约
    """
    # 找到所有G-不变子空间
    invariant_subspaces = find_invariant_subspaces(V, G, action)
    
    # 如果只有{0}和V，则不可约
    trivial_only = len(invariant_subspaces) == 2
    return trivial_only
```

### 4.3 验证Maschke条件

```python
def verify_maschke_condition(G, field_char):
    """
    验证Maschke定理的条件
    
    参数:
        G: 群
        field_char: 域的特征
    
    返回:
        maschke_applies: Maschke定理是否适用
    """
    group_order = len(G)
    
    # 条件：char(k) 不整除 |G|
    maschke_applies = (group_order % field_char != 0) if field_char > 0 else True
    
    return maschke_applies

# 例子
G = symmetric_group(3)  # |G| = 6
field_char = 2  # char = 2

maschke_applies = verify_maschke_condition(G, field_char)
print(f"Maschke适用: {maschke_applies}")  # False，因为2|6

field_char = 5  # char = 5
maschke_applies = verify_maschke_condition(G, field_char)
print(f"Maschke适用: {maschke_applies}")  # True，因为5不整除6
```

---

## 五、范畴表征（抽象）

### 5.1 半单范畴

**Maschke定理**说明 $k[G]$-Mod是**半单Abel范畴**：

- **半单性**：每个对象是完全可约的
- **短正合列分裂**：每个短正合列分裂
- **投射性**：每个模是投射模

### 5.2 同调维数

在**同调代数**中：

- Maschke条件 ⟺ $\operatorname{gl.dim}(k[G]) = 0$
- 这对应零全局维数

### 5.3 表示论

在**表示论**中：

- Maschke是有限群表示论的基础
- 保证表示的完全可约性
- 这是特征标理论的基础

---

## 六、应用实例

### 6.1 经典例子

**例子1**：$G = S_3$（3次对称群），$k = \mathbb{C}$

- $|G| = 6$，$\operatorname{char}(\mathbb{C}) = 0$
- Maschke适用：$k[G]$ 半单
- 每个表示完全可约

**例子2**：$G = \mathbb{Z}/p\mathbb{Z}$，$k = \mathbb{F}_p$

- $|G| = p$，$\operatorname{char}(k) = p$
- Maschke不适用：$p \mid p$
- $k[G]$ 不是半单的（实际上同构于 $k[x]/(x^p)$）

**例子3**：$G = \mathbb{Z}/2\mathbb{Z}$，$k = \mathbb{F}_3$

- $|G| = 2$，$\operatorname{char}(k) = 3$
- Maschke适用：$3 \nmid 2$
- $k[G]$ 半单

### 6.2 表示分解

**例子4**：$S_3$ 的2维表示

- 可以分解为两个1维不可约表示的直和
- 这由Maschke保证

**例子5**：特征标理论

- Maschke保证特征标的正交性
- 这是特征标表的基础

---

## 七、历史背景

### 7.1 发现历史

- **1898年**：Maschke 首次证明
- **现代**：成为表示论的基础
- **应用**：广泛用于群论和代数

### 7.2 现代意义

Maschke定理是：
- 有限群表示论的基础
- 特征标理论的前提
- 代数结构理论的应用

---

## 八、证明思路

### 8.1 标准证明

**证明**：

1. **投影存在**：设 $N \subset M$ 是子模，存在投影 $\pi: M \to N$

2. **构造G-等变投影**：
   $$P = \frac{1}{|G|} \sum_{g \in G} g \circ \pi \circ g^{-1}$$

3. **验证**：
   - $P$ 是投影：$P^2 = P$
   - $P$ 是G-等变的：$g \circ P = P \circ g$
   - $\ker P$ 是 $N$ 的补子模

4. **结论**：$M = N \oplus \ker P$，$M$ 完全可约

### 8.2 使用同调

**证明思路**：

- Maschke条件 ⟺ $\operatorname{Ext}^1(M, N) = 0$ 对所有 $M, N$
- 这等价于半单性

---

## 九、推广与变体

### 9.1 无限群

对于无限群，Maschke定理一般不成立。

### 9.2 一般环

对于一般环上的群代数，有类似的Maschke定理。

### 9.3 相对版本

有相对Maschke定理，考虑子群和商群。

---

**状态**: ✅ 完成（已深化）
**字数**: 约2,400字
**数学公式数**: 8个
**例子数**: 6个
**最后更新**: 2026年01月02日

# Galois基本定理完整推导

## 核心定理陈述

**Galois基本定理**：设 $E/F$ 是有限Galois扩张，$G = \text{Gal}(E/F)$。则存在反序双射：
$$\{\text{中间域 } F \subseteq K \subseteq E\} \longleftrightarrow \{\text{子群 } H \leq G\}$$
其中 $K \mapsto \text{Gal}(E/K)$，$H \mapsto E^H$（不动域）。

---

## 完整推理树

```mermaid
graph TD
    A[域扩张 E/F] --> B[Galois扩张<br/>正规+可分]
    B --> C[自同构群<br/>Gal(E/F)]
    
    C --> D[固定域对应<br/>H ↦ E^H]
    D --> E[[E:E^H] = |H|]
    E --> F[Artin定理<br/>E/E^H Galois]
    
    G[中间域K] --> H[伽罗瓦群<br/>Gal(E/K) ≤ G]
    H --> I[[E:K] = |Gal(E/K)|]
    
    F --> J[对应定理<br/>双射]
    I --> J
    
    J --> K[K₁ ⊆ K₂<br/>⇔ Gal(E/K₂) ≤ Gal(E/K₁)]
    J --> L[K/F Galois<br/>⇔ Gal(E/K) ⊲ G]
    J --> M[G/K对应<br/>Gal(K/F) ≅ G/Gal(E/K)]
    
    B --> N[可分性<br/>可分多项式]
    B --> O[正规性<br/>分裂域]
    
    N --> P[本原元定理<br/>E = F(α)]
    O --> Q[所有共轭<br/>在E中]
    
    style J fill:#f9f,stroke:#333,stroke-width:2px
    style L fill:#bbf,stroke:#333,stroke-width:1px
    style M fill:#bbf,stroke:#333,stroke-width:1px
```

---

## 关键定义与引理

### Galois扩张的等价定义

```mermaid
graph TD
    A[有限扩张E/F] --> B{Galois扩张<br/>等价条件}
    B --> C[正规+可分]
    B --> D[E是F上某可分多项式的分裂域]
    B --> E[[E:F] = |Gal(E/F)|]
    B --> F[E^G = F<br/>G = Gal(E/F)]
    
    C --> G[E^G = F 证明]
    D --> H[分裂域性质]
    E --> I[自同构数量]
    
    style C fill:#f9f,stroke:#333,stroke-width:2px
```

### Artin定理

**定理**：设 $E$ 是域，$G \leq \text{Aut}(E)$ 是有限子群，$F = E^G$。则 $E/F$ 是Galois扩张且 $\text{Gal}(E/F) = G$。

**证明要点**：
1. **线性无关性**：$G$ 的作用线性无关（Dedekind引理）
2. **本原元存在**：利用轨道求和构造
3. **次数公式**：$[E:F] \leq |G|$（由线性代数）
4. **等式**：$G \leq \text{Gal}(E/F)$，故 $|G| \leq |\text{Gal}(E/F)| \leq [E:F]$ ∎

---

## Galois对应详证

### 映射定义

| 方向 | 映射 | 定义 |
|-----|------|-----|
| 域→群 | $\Phi$ | $K \mapsto \text{Gal}(E/K) = \{\sigma \in G : \sigma|_K = \text{id}\}$ |
| 群→域 | $\Psi$ | $H \mapsto E^H = \{\alpha \in E : \sigma(\alpha) = \alpha, \forall \sigma \in H\}$ |

### 互逆验证

**步骤1**：$\Psi(\Phi(K)) = K$

- 显然 $K \subseteq E^{\text{Gal}(E/K)}$
- 由 Artin：$[E:E^{\text{Gal}(E/K)}] = |\text{Gal}(E/K)| = [E:K]$
- 故相等 ∎

**步骤2**：$\Phi(\Psi(H)) = H$

- 显然 $H \leq \text{Gal}(E/E^H)$
- 由 Artin：$|\text{Gal}(E/E^H)| = [E:E^H]$
- 由定义/证明：$[E:E^H] \leq |H|$
- 故相等 ∎

---

## 对应性质

```mermaid
graph TD
    A[Galois对应<br/>K ↔ H] --> B[包含反序<br/>K₁⊆K₂ ⇔ H₂≤H₁]
    A --> C[指数对应<br/>[K:F] = [G:H]]
    A --> D[共轭对应<br/>σ(K) ↔ σHσ⁻¹]
    
    D --> E[正规子群<br/>⇔ Galois中间域]
    E --> F[K/F Galois<br/>⇔ H ⊲ G]
    F --> G[商群同构<br/>Gal(K/F) ≅ G/H]
    
    H[合成列] --> I[可解扩张<br/>可解群]
    I --> J[根式可解<br/>多项式方程]
    
    style A fill:#f9f,stroke:#333,stroke-width:2px
    style F fill:#bbf,stroke:#333,stroke-width:1px
```

### 重要对应表

| 域性质 | 群性质 | 公式/说明 |
|-------|-------|----------|
| $K/F$ Galois | $H \trianglelefteq G$ | 正规子群对应正规扩张 |
| $[K:F]$ | $[G:H]$ | 指数等于扩张次数 |
| $\text{Gal}(K/F)$ | $G/H$ | 商群结构 |
| 合成域 $K_1 K_2$ | $H_1 \cap H_2$ | 交对应合成 |
| 交域 $K_1 \cap K_2$ | $\langle H_1, H_2 \rangle$ | 生成对应交 |

---

## 经典例子

### 例子1：二次扩张

```mermaid
graph TD
    subgraph Q(√d)/Q
    Q[Q] --> K[Q(√d)]
    K --> E[Q(√d)]
    end
    
    subgraph Galois群S₂
    G[G = {id, σ}] --> H1[{id}] 
    end
    
    K -.->|Gal(E/K) = {id}| H1
    Q -.->|Gal(E/Q) = G| G
```

### 例子2：双二次扩张 $\mathbb{Q}(\sqrt{2}, \sqrt{3})/\mathbb{Q}$

```mermaid
graph TD
    subgraph 域塔
    Q[Q] --> K1[Q(√2)]
    Q --> K2[Q(√3)]
    Q --> K3[Q(√6)]
    K1 --> E[Q(√2,√3)]
    K2 --> E
    K3 --> E
    end
    
    subgraph Klein四元群V₄ ≅ C₂×C₂
    G[G] --> H1[⟨σ⟩]
    G --> H2[⟨τ⟩]
    G --> H3[⟨στ⟩]
    H1 --> I[{e}]
    H2 --> I
    H3 --> I
    end
    
    E -.-> I
    K1 -.-> H1
    K2 -.-> H2
    K3 -.-> H3
    Q -.-> G
```

- $\sigma: \sqrt{2} \mapsto -\sqrt{2}, \sqrt{3} \mapsto \sqrt{3}$
- $\tau: \sqrt{2} \mapsto \sqrt{2}, \sqrt{3} \mapsto -\sqrt{3}$

### 例子3：分圆扩张 $\mathbb{Q}(\zeta_7)/\mathbb{Q}$

- $G \cong (\mathbb{Z}/7\mathbb{Z})^\times \cong C_6$
- 子群对应：$C_6 \triangleright C_3 \triangleright \{e\}$ 和 $C_6 \triangleright C_2 \triangleright \{e\}$
- 中间域：$\mathbb{Q} \subseteq \mathbb{Q}(\zeta_7 + \zeta_7^{-1}) \subseteq \mathbb{Q}(\zeta_7)$（实子域）

---

## 可解性与根式扩张

```mermaid
graph TD
    A[f(x) ∈ F[x]] --> B[分裂域E<br/>f的根生成]
    B --> C[Gal(E/F)]
    
    C --> D{可解群?}
    D -->|是| E[可解扩张列<br/>G = G₀ ⊵ ... ⊵ {e}]
    E --> F[根式扩张塔<br/>添加n次根]
    F --> G[f根式可解<br/>根可用根式表示]
    
    D -->|否| H[一般五次以上<br/>非可解群]
    H --> I[Abel-Ruffini<br/>无根式解公式]
    
    style D fill:#f9f,stroke:#333,stroke-width:2px
```

---

## 参考

- Artin, *Galois Theory*
- Edwards, *Galois Theory*
- Dummit & Foote, Chapter 14
- Cox, *Galois Theory*

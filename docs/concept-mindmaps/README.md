---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 几何与拓扑学概念思维导图索引

本目录包含几何与拓扑学核心概念的Markdown格式思维导图，使用Mermaid语法绘制。

---

## 📚 目录结构

### 一、拓扑学基础 (6个)

| 概念 | 文件 | 核心内容 |
|------|------|---------|
| **拓扑空间** | [topology-topological-space.md](./topology-topological-space.md) | 开集公理、拓扑构造、基本性质 |
| **连续映射** | [topology-continuous-map.md](./topology-continuous-map.md) | 连续性定义、同胚、诱导拓扑、同伦 |
| **连通性** | [topology-connectedness.md](./topology-connectedness.md) | 连通、道路连通、局部连通、单连通 |
| **紧致性** | [topology-compactness.md](./topology-compactness.md) | 紧致空间、局部紧致、Tychonoff定理 |
| **分离公理** | [topology-separation-axioms.md](./topology-separation-axioms.md) | T₀-T₆公理、Urysohn引理、可度量化 |
| **商空间** | [topology-quotient-space.md](./topology-quotient-space.md) | 商映射、叠合空间、胞腔结构 |

### 二、代数拓扑 (6个)

| 概念 | 文件 | 核心内容 |
|------|------|---------|
| **基本群** | [algebraic-fundamental-group.md](./algebraic-fundamental-group.md) | π₁定义、van Kampen定理、计算方法 |
| **覆叠空间** | [algebraic-covering-space.md](./algebraic-covering-space.md) | 覆叠映射、提升性质、万有覆叠、分类定理 |
| **同调群** | [algebraic-homology.md](./algebraic-homology.md) | 单纯/奇异同调、正合序列、Mayer-Vietoris |
| **上同调** | [algebraic-cohomology.md](./algebraic-cohomology.md) | Cup积、de Rham定理、Poincaré对偶 |
| **同伦论** | [algebraic-homotopy.md](./algebraic-homotopy.md) | 高阶同伦群、纤维化、CW复形、谱序列 |
| **纤维丛** | [algebraic-fiber-bundle.md](./algebraic-fiber-bundle.md) | 向量丛、主丛、示性类、分类空间 |

### 三、微分几何 (6个)

| 概念 | 文件 | 核心内容 |
|------|------|---------|
| **微分流形** | [dg-manifold.md](./dg-manifold.md) | 光滑结构、子流形、Whitney嵌入、定向 |
| **切空间** | [dg-tangent-space.md](./dg-tangent-space.md) | 切丛、余切丛、向量场、Frobenius定理 |
| **张量分析** | [dg-tensor.md](./dg-tensor.md) | 张量代数、微分形式、Lie导数、协变导数 |
| **黎曼度量** | [dg-riemannian-metric.md](./dg-riemannian-metric.md) | 内积结构、Levi-Civita联络、完备性、等距 |
| **曲率** | [dg-curvature.md](./dg-curvature.md) | Riemann张量、截面曲率、Ricci曲率、Gauss-Bonnet |
| **测地线** | [dg-geodesic.md](./dg-geodesic.md) | 自平行曲线、指数映射、Jacobi场、Hopf-Rinow |

### 四、代数几何 (4个)

| 概念 | 文件 | 核心内容 |
|------|------|---------|
| **代数簇** | [algebraic-geometry-variety.md](./algebraic-geometry-variety.md) | 仿射/射影簇、Zariski拓扑、Hilbert定理 |
| **概形** | [algebraic-geometry-scheme.md](./algebraic-geometry-scheme.md) | Spec、结构层、态射、算术几何 |
| **层** | [algebraic-geometry-sheaf.md](./algebraic-geometry-sheaf.md) | 预层与层、凝聚层、层上同调、Serre对偶 |
| **上同调** | [algebraic-geometry-cohomology.md](./algebraic-geometry-cohomology.md) | ℓ进上同调、晶体上同调、Weil猜想、motive |

---

## 🔗 概念关联图

```

拓扑学基础
    │
    ├── 拓扑空间 → 连续映射 → 同胚
    ├── 连通性 → 道路连通 → 单连通
    ├── 紧致性
    ├── 分离公理
    └── 商空间
         │
         ↓
代数拓扑
    │
    ├── 基本群 ───────→ 覆叠空间
    │      ↓                ↓
    │   同伦论 ←─────── 纤维丛
    │      ↓                ↓
    └── 同调群 ←──────→ 上同调 (Cup积)
              ↓
         de Rham定理
              ↓
微分几何
    │
    ├── 微分流形 ────→ 切空间
    │      ↓              ↓
    ├── 张量分析 ←────── 切丛/余切丛
    │      ↓
    ├── 黎曼度量 ────→ 曲率
    │      ↓              ↓
    └── 测地线 ←─────── Levi-Civita联络
         ↓
代数几何
    │
    ├── 代数簇
    │      ↓
    ├── 概形 ────────→ 层
    │      ↓              ↓
    └── 上同调 ←─────── 凝聚层上同调
              ↓
         ℓ进/晶体上同调

```

---

## 📖 使用说明

### 查看思维导图

1. **GitHub/GitLab**: 直接在线查看Markdown文件，Mermaid图表会自动渲染
2. **VS Code**: 安装Mermaid插件后本地预览
3. **Typora/MarkText**: 支持Mermaid的Markdown编辑器
4. **在线工具**: 使用[Mermaid Live Editor](https://mermaid.live)粘贴代码

### 思维导图特点

- 每个文件包含：
  - **概述**: 概念简介
  - **Mermaid思维导图**: 可视化知识结构
  - **核心要点**: 表格形式的精华总结
  - **重要定理**: 关键数学结果
  - **关联概念**: 相关文件的链接

---

## 📊 统计信息

| 类别 | 文件数 | 总概念节点数 |
|------|--------|-------------|
| 拓扑学基础 | 6 | ~120 |
| 代数拓扑 | 6 | ~140 |
| 微分几何 | 6 | ~150 |
| 代数几何 | 4 | ~100 |
| **总计** | **22** | **~510** |

---

## 🔍 快速检索

### 按数学领域

- **纯拓扑**: topology-*
- **代数拓扑**: algebraic-*
- **微分几何**: dg-*
- **代数几何**: algebraic-geometry-*

### 按核心主题

- **基本结构**: 拓扑空间、微分流形、代数簇
- **映射理论**: 连续映射、覆叠空间、纤维丛
- **不变量**: 同调、上同调、曲率
- **几何对象**: 测地线、层、概形

---

## 📚 学习建议

### 入门路径

1. **拓扑学基础** → 理解连续性和拓扑不变量
2. **基本群** → 首个代数不变量
3. **微分流形** → 进入光滑几何世界
4. **黎曼度量** → 测量和曲率
5. **层论** → 现代几何语言

### 进阶路径

1. **同调/上同调** → 系统的不变量理论
2. **纤维丛/示性类** → 几何与拓扑的桥梁
3. **概形** → 现代代数几何基础
4. **motive理论** → 统一上同调观点

---

*生成日期: 2026年4月4日*

*格式: Markdown + Mermaid*

# Atiyah-Singer指标定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微分几何/代数拓扑
**难度**: L4

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Atiyah-Singer指标定理 |
| **领域** | 微分几何/代数拓扑 |
| **发现者** | Atiyah, Singer (1963) |
| **前置知识** | 椭圆算子、K理论、示性类 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Atiyah-Singer指标定理**：设M是紧致定向流形，D是M上的椭圆算子，则：

$$\mathrm{ind}(D) = \dim\ker D - \dim\ker D^* = \int_M \mathrm{ch}(D) \wedge \mathrm{Td}(M)$$

分析指标（左）= 拓扑指标（右）

---

## 二、几何表征（可视化）

```text
椭圆算子D
    │
    ├── 分析：ker D 和 coker D 的维数差
    │
    └── 拓扑：示性类的积分

两者相等！
```

---

## 三、直觉表征（类比）

> **指标定理**：微分方程解的"数量"由空间的拓扑决定

---

## 四、计算表征（算法）

```python
def index_euler_characteristic(M_triangulation):
    # 特例：Euler特征 = Σ(-1)^k b_k
    return sum((-1)**k * betti[k] for k in range(dim+1))
```

---

## 五、范畴表征（抽象）

指标定理是分析（椭圆算子）与拓扑（K理论）之间的同构。

---

**状态**: ✅ 完成

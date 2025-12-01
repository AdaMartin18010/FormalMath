# Perron-Frobenius定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 线性代数/马尔可夫链
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Perron-Frobenius定理 |
| **领域** | 线性代数 |
| **发现者** | Perron (1907), Frobenius (1912) |
| **前置知识** | 非负矩阵、特征值 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Perron-Frobenius定理**：设A是不可约非负矩阵，则：
1. A有唯一最大特征值r > 0（Perron根）
2. r是单特征值
3. 对应的特征向量分量全正

---

## 二、几何表征（可视化）

```text
不可约非负矩阵的谱：

    │  r (Perron根，最大)
    │  │
──●─●─┼─●─●── 实轴
      0
    其他特征值|λ| < r
```

---

## 三、直觉表征（类比）

> **Perron-Frobenius**：非负矩阵有一个"主导"特征值，对应全正特征向量

---

## 四、计算表征（算法）

```python
def power_method_perron(A, max_iter=1000, tol=1e-10):
    v = np.ones(A.shape[0])
    for _ in range(max_iter):
        v_new = A @ v
        r = np.linalg.norm(v_new)
        v_new /= r
        if np.linalg.norm(v_new - v) < tol:
            break
        v = v_new
    return r, v  # Perron根和特征向量
```

---

## 五、范畴表征（抽象）

Perron-Frobenius反映非负矩阵的半群结构，在PageRank等应用中核心。

---

**状态**: ✅ 完成

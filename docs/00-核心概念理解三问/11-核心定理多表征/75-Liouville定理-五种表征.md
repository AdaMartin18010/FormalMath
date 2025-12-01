# Liouville定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 复分析
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Liouville定理 |
| **领域** | 复分析 |
| **发现者** | Joseph Liouville |
| **前置知识** | 整函数、有界性 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Liouville定理**：有界整函数是常数。

若f: ℂ → ℂ全纯且|f(z)| ≤ M对所有z，则f是常数。

---

## 二、几何表征（可视化）

```text
整函数（全复平面全纯）：

    有界 ⟹ 常数

    非常数整函数必无界
```

---

## 三、直觉表征（类比）

> **Liouville**：全纯函数"太刚性"，有界必为常数

---

## 四、计算表征（算法）

```python
def check_liouville(f, bound=1000, n_samples=1000):
    # 如果f有界且全纯，则应为常数
    z_samples = [complex(r*np.cos(t), r*np.sin(t))
                for r in [1, 10, 100] for t in np.linspace(0, 2*np.pi, n_samples)]
    values = [f(z) for z in z_samples]
    return np.std(values) < 1e-6  # 近似常数
```

---

## 五、范畴表征（抽象）

Liouville定理由Cauchy估计推出，反映全纯函数的刚性。

---

**状态**: ✅ 完成

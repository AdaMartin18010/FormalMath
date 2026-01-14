# Green定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 向量分析
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Green定理 |
| **领域** | 向量分析 |
| **发现者** | George Green (1828) |
| **前置知识** | 线积分、二重积分 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Green定理**：设D是平面上由简单闭曲线C围成的区域，则：

$$\oint_C (P\,dx + Q\,dy) = \iint_D \leqft(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\right) dA$$

---

## 二、几何表征（可视化）

```text
边界积分 = 内部积分

    ∮_C = ∬_D (旋度)
```

---

## 三、直觉表征（类比）

> **Green**：沿边界的环流 = 内部旋度的总和

---

## 四、计算表征（算法）

```python
def green_verify(P, Q, C_integral, D_area_integral):
    # 左边：线积分
    # 右边：∂Q/∂x - ∂P/∂y 的面积分
    return np.isclose(C_integral, D_area_integral)
```

---

## 五、范畴表征（抽象）

Green定理是Stokes定理在二维的特例：∫_∂D ω = ∫_D dω。

---

**状态**: ✅ 完成

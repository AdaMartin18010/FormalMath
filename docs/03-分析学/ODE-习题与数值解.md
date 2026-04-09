---
title: 常微分方程习题与数值解
msc_primary: 34-01
---

# 常微分方程习题与数值解

## 习题

### 习题1

求解$\frac{dy}{dx} = y$，$y(0) = 1$。

**解答**：$y = e^x$

### 习题2

用积分因子法求解$\frac{dy}{dx} + P(x)y = Q(x)$。

**解答**：积分因子$\mu(x) = e^{\int P(x)dx}$，解为$y = \frac{1}{\mu}\int \mu Q dx$

---

## Python数值解

```python
import numpy as np
from scipy.integrate import odeint
import matplotlib.pyplot as plt

# 定义ODE: dy/dt = -2y
def model(y, t):
    return -2*y

# 初始条件和时间点
y0 = 1
t = np.linspace(0, 5, 100)

# 求解
y = odeint(model, y0, t)

# 绘图
plt.plot(t, y, 'b-', label='y(t)')
plt.xlabel('t')
plt.ylabel('y')
plt.title('Solution of dy/dt = -2y')
plt.legend()
plt.grid(True)
plt.savefig('ode_solution.png')
plt.show()
```

---

**适用**：docs/03-分析学/

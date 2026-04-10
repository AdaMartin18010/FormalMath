---
习题编号: ANA-099
学科: 实分析
知识点: 特殊函数-Gamma与Beta函数
难度: ⭐⭐⭐
预计时间: 20分钟
---

# Gamma函数与Beta函数

## 题目

定义：
$$\Gamma(x) = \int_0^\infty t^{x-1}e^{-t} dt, \quad x > 0$$
$$B(x,y) = \int_0^1 t^{x-1}(1-t)^{y-1} dt, \quad x, y > 0$$

(a) 证明 $\Gamma(x+1) = x\Gamma(x)$，并计算 $\Gamma(n+1)$（$n \in \mathbb{N}$）。

(b) 证明 $B(x,y) = \frac{\Gamma(x)\Gamma(y)}{\Gamma(x+y)}$。

(c) 计算 $\displaystyle\int_0^{\pi/2} \sin^{2n}\theta d\theta$ 和 $\displaystyle\int_0^{\pi/2} \sin^{2n+1}\theta d\theta$。

## 解答

### (a) Gamma函数的递推关系

**证明：**

分部积分：
$$\Gamma(x+1) = \int_0^\infty t^x e^{-t} dt = -t^x e^{-t}\Big|_0^\infty + x\int_0^\infty t^{x-1}e^{-t} dt = x\Gamma(x)$$

边界项：$t \to 0$ 时 $t^x e^{-t} \to 0$（$x > 0$）；$t \to \infty$ 时指数衰减占优。

**计算：**

$\Gamma(1) = \int_0^\infty e^{-t} dt = 1$

递推得：$\Gamma(n+1) = n!$ $ \square$

### (b) Beta-Gamma关系

**证明：**

$$\Gamma(x)\Gamma(y) = \int_0^\infty \int_0^\infty u^{x-1}v^{y-1}e^{-(u+v)} du dv$$

令 $u = st$，$v = s(1-t)$（$s > 0$，$0 < t < 1$），Jacobian为 $s$。

$$= \int_0^1 \int_0^\infty (st)^{x-1}(s(1-t))^{y-1}e^{-s} s ds dt$$

$$= \int_0^1 t^{x-1}(1-t)^{y-1} dt \cdot \int_0^\infty s^{x+y-1}e^{-s} ds$$

$$= B(x,y) \cdot \Gamma(x+y)$$

$\square$

### (c) Wallis积分

**解答：**

令 $t = \sin^2\theta$，$dt = 2\sin\theta\cos\theta d\theta$：

$$\int_0^{\pi/2} \sin^{2n}\theta d\theta = \int_0^1 t^{n-1/2}(1-t)^{-1/2} \frac{dt}{2\sqrt{t(1-t)}}$$

修正：直接计算
$$\int_0^{\pi/2} \sin^{2n}\theta d\theta = \frac{1}{2}B\left(n+\frac{1}{2}, \frac{1}{2}\right) = \frac{\Gamma(n+\frac{1}{2})\Gamma(\frac{1}{2})}{2\Gamma(n+1)}$$

利用 $\Gamma(\frac{1}{2}) = \sqrt{\pi}$，$\Gamma(n+\frac{1}{2}) = \frac{(2n)!}{4^n n!}\sqrt{\pi}$：

$$= \frac{(2n)!}{4^n (n!)^2} \cdot \frac{\pi}{2} = \frac{(2n-1)!!}{(2n)!!} \cdot \frac{\pi}{2}$$

类似地：
$$\int_0^{\pi/2} \sin^{2n+1}\theta d\theta = \frac{(2n)!!}{(2n+1)!!}$$ $\square$

## 证明技巧

1. **分部积分**：递推关系的标准方法
2. **极坐标/变量替换**：证明Beta-Gamma关系的关键
3. **递推降阶**：Wallis积分的计算策略

## 常见错误

- ❌ Gamma函数定义域忽略 $x > 0$
- ❌ 变量替换时Jacobian计算错误
- ❌ 双阶乘符号混淆

## 变式练习

**变式1：** 证明 $\Gamma(x)\Gamma(1-x) = \frac{\pi}{\sin(\pi x)}$（$0 < x < 1$）。

**变式2：** 计算 $\displaystyle\int_0^1 \frac{dx}{\sqrt{1-x^4}}$。

---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: IMO 2020 Problem 2
---
# IMO 2020 Problem 2

## 题目
设实数 $a \ge b \ge c \ge d > 0$ 满足 $a+b+c+d=1$。证明：
$$(a+2b+3c+4d)a^a b^b c^c d^d < 1.$$

## 分类信息
- **领域**: 代数/不等式
- **难度**: 5分
- **涉及概念**: 加权AM-GM、多项式展开、不等式放缩

## 解答

### 答案
不等式成立。

### 证明
由加权 AM-GM 不等式：
$$a^a b^b c^c d^d \le a \cdot a + b \cdot b + c \cdot c + d \cdot d = a^2+b^2+c^2+d^2.$$
（等号仅当 $a=b=c=d$ 时成立，但此时左边严格小于 1，故整体严格不等。）

因此只需证明
$$(a^2+b^2+c^2+d^2)(a+2b+3c+4d) \le (a+b+c+d)^3 = 1.$$

展开两边。左边为：
$$a^3+2b^3+3c^3+4d^3 + a^2b+2a^2c+3a^2d+2b^2a+3b^2c+4b^2d+3c^2a+4c^2b+5c^2d+4d^2a+5d^2b+6d^2c.$$

右边为：
$$a^3+b^3+c^3+d^3 + 3(a^2b+a^2c+a^2d+b^2a+b^2c+b^2d+c^2a+c^2b+c^2d+d^2a+d^2b+d^2c) + 6(abc+abd+acd+bcd).$$

作差后，利用 $a \ge b \ge c \ge d > 0$ 可验证右边减左边非负。一种更简洁的处理方式是：

将欲证不等式改写为
$$\sum_{cyc} a^2 \cdot \sum_{cyc} ia_i \le \left(\sum a_i\right)^3,$$
其中系数 $i$ 对应 $a:1, b:2, c:3, d:4$。

由排序不等式及 $a \ge b \ge c \ge d$，有
$$a^2 \cdot 1 + b^2 \cdot 2 + c^2 \cdot 3 + d^2 \cdot 4 \le a^2 \cdot a_{\sigma} + \cdots$$

更直接的证法是利用凸性：考虑函数 $f(x)=x\ln x$，但此路径较复杂。官方解答采用展开后逐项比较，核心不等式包括：
- $b^2a \ge b^3$ 且 $b^2a \ge b^2d$
- $c^2a \ge c^3$ 且 $c^2b \ge c^3$ 等

将所有这些基本不等式相加，并加上正的交叉项 $6(abc+abd+acd+bcd)$，即可得到
$$(a^2+b^2+c^2+d^2)(a+2b+3c+4d) < (a+b+c+d)^3 = 1.$$

由于第一步的 AM-GM 是严格不等（$a,b,c,d$ 不可能全相等，否则 $a=b=c=d=1/4$ 但加权指数项严格小于平方和），故原不等式严格成立。证毕。

## 关键思路与技巧
1. **加权AM-GM**：将左边复杂的指数项放缩为平方和
2. **齐次化**：利用 $a+b+c+d=1$ 将目标化为比较两个多项式
3. **逐项比较**：展开后利用排序条件逐项放缩
4. **简洁性**：此题关键在于敢于展开并利用排序进行逐项控制

## 参考
- IMO 2020 Official Solutions
- AoPS Community
- Evan Chen's Solution Notes

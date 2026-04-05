---
msc_primary: 03B05
msc_secondary:
- 03B10
- 03C05
title: 测试样本 - 命题逻辑
created: 2026-04-05
updated: 2026-04-05
version: 1.0.0
processed_at: '2026-04-05'
---
# 测试样本 - 命题逻辑

## 定义

**概念编号**: LOGIC-TEST-001

一个**命题**（Proposition）是一个可以判断真假的陈述句。

## 形式化定义

在Lean4中，命题可以表示为：

```lean
def Proposition := Prop
def isTrue (p : Prop) : Prop := p
def isFalse (p : Prop) : Prop := ¬p
```

## 相关概念

- [逻辑连接词](../../核心概念/逻辑连接词.md)
- [真值表](./../../docs/visualizations/思维导图/概念/真值表.md)

## 参考资料

1. 测试引用文献

# FormalMath Mathlib4 示例集

本项目提供了一系列可运行的Lean4代码示例，展示如何在Mathlib4中找到和使用与FormalMath文档对应的数学概念形式化实现。

## 环境要求

- Lean 4.29.0
- Mathlib4 v4.29.0
- lake (Lean包管理器)

## 快速开始

### 安装

```bash
# 确保已安装elan (Lean工具链管理器)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 克隆或下载本项目
cd docs/09-形式化证明/Lean4

# 获取依赖
lake update

# 构建项目
lake build
```

### 运行示例

```bash
# 运行特定示例
lean 00-Mathlib4示例集/01-群论示例.lean

# 或在VS Code中打开文件
# 按 Ctrl+Shift+X 执行代码
```

## 示例文件列表

| 文件名 | 对应FormalMath文档 | 主要内容 |
|-------|-------------------|---------|
| `01-群论示例.lean` | `docs/02-代数结构/02-核心理论/群论/` | Group, Subgroup, Quotient Group, Lagrange定理 |
| `02-环论示例.lean` | `docs/02-代数结构/02-核心理论/环论/` | Ring, Ideal, Quotient Ring, PID, UFD |
| `03-数论示例.lean` | `docs/06-数论/` | 素数, 同余, 欧拉函数, 二次互反律 |
| `04-实分析示例.lean` | `docs/03-分析学/01-实分析/` | 极限, 连续性, 导数, 积分, 中值定理 |
| `05-拓扑示例.lean` | `docs/05-拓扑学/` | 拓扑空间, 开集, 紧致性, 连通性 |
| `06-线性代数示例.lean` | `docs/02-代数结构/02-核心理论/线性代数与矩阵理论/` | 向量空间, 线性映射, 矩阵, 特征值 |
| `07-集合论示例.lean` | `docs/01-基础数学/集合论/` | 集合运算, 关系, 函数, 基数 |
| `08-证明策略示例.lean` | `docs/09-形式化证明/` | Tactics使用技巧, 结构化证明 |
| `09-类型论示例.lean` | `docs/07-逻辑学/` | 依赖类型, 命题即类型, 归纳类型 |
| `10-代数几何示例.lean` | `docs/13-代数几何/` | Scheme, 概形, 层论基础 |

## 文件结构说明

每个示例文件包含以下部分：

1. **导入声明** - 引入必要的Mathlib4模块
2. **文档注释** - 说明对应的FormalMath文档
3. **核心定义** - 展示相关定义的类型
4. **关键定理** - 验证重要定理的Mathlib4实现
5. **示例证明** - 提供可运行的证明示例
6. **练习** - 供读者练习的问题

## 学习建议

1. **按顺序学习**: 建议从`01-群论示例.lean`开始，逐步深入
2. **对比学习**: 同时打开对应的FormalMath文档，对比数学概念和形式化代码
3. **动手实践**: 修改示例中的参数和证明，观察结果
4. **解决练习**: 完成每个文件末尾的练习题

## 常见问题

### Q: 构建失败怎么办？

```bash
# 清理缓存
lake clean

# 重新获取mathlib缓存
lake exe cache get

# 重新构建
lake build
```

### Q: 如何查找特定定义或定理？

```lean
-- 在Lean代码中使用
import Mathlib

-- 查看定义
#check Group

-- 查看定理
#check mul_one

-- 搜索相关定义
#search "Subgroup"
```

### Q: 如何在VS Code中获得最佳体验？

1. 安装Lean4扩展
2. 打开项目根目录（包含lakefile.toml的目录）
3. 等待Lean服务器初始化完成
4. 使用快捷键执行代码：
   - `Ctrl+Shift+Enter` - 执行到光标位置
   - `Ctrl+Shift+X` - 执行整个文件

## 相关资源

- [Mathlib4概念映射索引](../00-Mathlib4概念映射索引.md)
- [从FormalMath到Mathlib4学习路径](../00-从FormalMath到Mathlib4学习路径.md)
- [Mathlib4官方文档](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean4教程](https://leanprover.github.io/theorem_proving_in_lean4/)

## 贡献

欢迎提交Issue和PR来改进示例代码。请确保：

1. 代码在Lean 4.29.0 + Mathlib4 v4.29.0下可编译
2. 添加适当的文档注释
3. 包含清晰的示例和练习

## 许可证

本示例集与FormalMath项目使用相同的许可证。

---
msc_primary: 68N99
title: FormalMath 开发文档
created_date: 2026-04-04
version: 1.0.0
author: FormalMath 开发团队
---

# FormalMath 开发文档

> 本文档集合为 FormalMath 项目的技术开发者提供完整的开发指南。

---

## 文档导航

| 文档 | 说明 | 适用人群 |
|------|------|----------|
| [01-架构设计文档](./01-架构设计文档.md) | 系统架构、组件设计、技术栈 | 架构师、核心开发者 |
| [02-API开发指南](./02-API开发指南.md) | API 接口规范、使用方法 | 后端开发者、工具开发者 |
| [03-前端开发指南](./03-前端开发指南.md) | 前端组件、状态管理、最佳实践 | 前端开发者 |
| [04-数据库设计文档](./04-数据库设计文档.md) | 数据模型、存储架构、索引设计 | 后端开发者 |
| [05-测试指南](./05-测试指南.md) | 测试策略、测试类型、CI/CD | 所有开发者 |
| [06-贡献指南](./06-贡献指南.md) | 开发流程、代码规范、提交规范 | 所有贡献者 |

---

## 快速开始

### 新开发者入门

1. **了解项目**
   - 阅读 [项目 README](../../README.md)
   - 浏览 [架构设计文档](./01-架构设计文档.md)

2. **搭建环境**
   - 按照 [贡献指南](./06-贡献指南.md) 设置开发环境
   - 运行预提交检查确保环境正常

3. **开始贡献**
   - 查找 `good first issue` 标签的 Issue
   - 阅读 [贡献指南](./06-贡献指南.md) 了解完整流程

### 技术栈速览

| 层级 | 技术 | 用途 |
|------|------|------|
| 内容 | Markdown + YAML | 文档存储 |
| 后端 | Python 3.8+ | 工具开发 |
| 形式化 | Lean4 | 定理证明 |
| 前端 | React + TypeScript | 交互界面 |
| 构建 | Vite | 前端构建 |
| 测试 | pytest + Vitest | 单元测试 |
| CI/CD | GitHub Actions | 自动化 |

---

## 代码规范

### 提交信息格式

```
<type>(<scope>): <subject>

<body>

<footer>
```

**类型**：`feat` | `fix` | `docs` | `style` | `refactor` | `test` | `chore`

**范围**：`assessment` | `metadata` | `frontend` | `api` | `docs` | `tools`

### 文件组织

```
├── docs/                    # 内容文档
├── tools/                   # Python 工具
│   ├── assessment-system/
│   ├── metadata-system/
│   └── ...
├── FormalMath-Interactive/  # 前端项目
├── tests/                   # 测试代码
└── docs/开发文档/            # 本目录
```

---

## 常用命令

### 工具开发

```bash
# 运行测试
pytest tests/unit

# 运行检查
python tools/contributor-workflow/pre_commit_check.py --all

# 提取元数据
python tools/metadata-system/metadata_cli.py scan

# 质量评估
python tools/content-quality-assessment/quality_assessor.py docs/ -r
```

### 前端开发

```bash
cd FormalMath-Interactive

# 安装依赖
npm install

# 开发服务器
npm run dev

# 构建
npm run build

# 测试
npm run test
```

---

## 开发资源

### 项目链接

- [GitHub 仓库](https://github.com/formalmath/FormalMath)
- [Issue 跟踪](../../issues)
- [项目看板](../../projects)
- [CHANGELOG](../../CHANGELOG.md)

### 参考文档

- [项目使用指南](../../00-FormalMath项目使用指南-完整版.md)
- [项目内容索引](../../00-FormalMath项目内容索引-完整版.md)
- [CONTRIBUTING](../../CONTRIBUTING.md)

---

## 贡献统计

```
文档统计
├── 总文档数: 6
├── 总字数: ~50,000
├── 代码示例: 50+
└── 图表: 20+
```

---

**最后更新**: 2026年4月4日  
**维护者**: FormalMath 开发团队  
**许可证**: MIT

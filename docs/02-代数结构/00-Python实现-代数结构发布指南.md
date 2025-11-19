# 代数结构Python实现发布指南

## 概述

本文档提供代数结构Python实现的完整发布指南，包括版本管理、发布流程、发布检查清单和发布后工作。

## 目录

- [版本管理](#版本管理)
- [发布流程](#发布流程)
- [发布检查清单](#发布检查清单)
- [发布后工作](#发布后工作)
- [回滚流程](#回滚流程)
- [常见问题](#常见问题)

## 版本管理

### 语义化版本

项目遵循[语义化版本规范](https://semver.org/)：`MAJOR.MINOR.PATCH`

- **MAJOR** (主版本号): 不兼容的API变更
- **MINOR** (次版本号): 向后兼容的功能新增
- **PATCH** (修订版本号): 向后兼容的问题修复

### 版本号示例

```
1.0.0  # 初始发布
1.0.1  # Bug修复
1.1.0  # 新功能
1.1.1  # Bug修复
2.0.0  # 重大变更（不兼容）
```

### 预发布版本

- **alpha**: `1.1.0-alpha.1` - 内部测试版本
- **beta**: `1.1.0-beta.1` - 公开测试版本
- **rc**: `1.1.0-rc.1` - 发布候选版本

## 发布流程

### 1. 发布前准备

#### 1.1 代码审查

- [ ] 所有Pull Request已审查并合并
- [ ] 代码符合项目规范
- [ ] 所有测试通过
- [ ] 测试覆盖率达标（≥80%）

#### 1.2 文档更新

- [ ] 更新变更日志（CHANGELOG.md）
- [ ] 更新README（如有重大变更）
- [ ] 更新API文档
- [ ] 更新用户指南（如有新功能）

#### 1.3 测试验证

```bash
# 运行所有测试
pytest

# 检查测试覆盖率
pytest --cov=algebraic_structures --cov-report=term --cov-fail-under=80

# 运行性能测试
pytest tests/test_performance.py

# 运行集成测试
pytest tests/test_integration.py
```

### 2. 版本号确定

#### 2.1 检查变更类型

```bash
# 查看自上次发布以来的变更
git log v1.0.0..HEAD --oneline

# 分析变更类型
# - 是否有破坏性变更？→ MAJOR
# - 是否有新功能？→ MINOR
# - 是否只有Bug修复？→ PATCH
```

#### 2.2 确定版本号

- **MAJOR**: API不兼容变更、重大重构
- **MINOR**: 新功能、新算法、新工具
- **PATCH**: Bug修复、性能优化、文档更新

### 3. 创建发布分支

```bash
# 从main分支创建发布分支
git checkout -b release/v1.1.0 main

# 推送发布分支
git push origin release/v1.1.0
```

### 4. 更新版本号

#### 4.1 更新版本文件

创建或更新 `algebraic_structures/__version__.py`:

```python
"""版本信息"""
__version__ = "1.1.0"
__version_info__ = (1, 1, 0)
```

#### 4.2 更新setup.py

```python
setup(
    name="algebraic-structures",
    version="1.1.0",
    # ...
)
```

#### 4.3 更新文档

更新所有文档中的版本号引用。

### 5. 更新变更日志

在 `CHANGELOG.md` 中添加新版本条目：

```markdown
## [1.1.0] - 2025-01-15

### 新增
- 添加了新的群表示算法
- 添加了可视化工具

### 变更
- 改进了性能优化机制

### 修复
- 修复了循环群计算的Bug

### 文档
- 更新了API参考文档
```

### 6. 创建Git标签

```bash
# 创建带注释的标签
git tag -a v1.1.0 -m "Release version 1.1.0"

# 推送标签
git push origin v1.1.0
```

### 7. 构建发布包

#### 7.1 构建源代码包

```bash
# 清理之前的构建
rm -rf dist/ build/ *.egg-info

# 构建源代码包
python setup.py sdist

# 构建wheel包
python setup.py bdist_wheel
```

#### 7.2 验证构建

```bash
# 检查构建的包
ls -lh dist/

# 验证wheel包
python -m pip install --upgrade twine
twine check dist/*
```

### 8. 测试发布包

```bash
# 在虚拟环境中测试安装
python -m venv test_env
source test_env/bin/activate  # Linux/macOS
# 或
test_env\Scripts\activate  # Windows

# 安装测试包
pip install dist/algebraic_structures-1.1.0-py3-none-any.whl

# 测试导入
python -c "import algebraic_structures; print(algebraic_structures.__version__)"

# 运行基本测试
python -c "from algebraic_structures.groups import cyclic_group; G = cyclic_group(6); print(G.order())"
```

### 9. 发布到PyPI

#### 9.1 测试PyPI（可选）

```bash
# 上传到测试PyPI
twine upload --repository-url https://test.pypi.org/legacy/ dist/*

# 从测试PyPI安装测试
pip install --index-url https://test.pypi.org/simple/ algebraic-structures
```

#### 9.2 正式发布

```bash
# 上传到PyPI
twine upload dist/*

# 需要PyPI凭据
# Username: __token__
# Password: pypi-xxxxxxxxxxxxx
```

### 10. 创建GitHub Release

1. 访问GitHub仓库
2. 点击"Releases" → "Draft a new release"
3. 选择标签: `v1.1.0`
4. 填写发布标题: `Version 1.1.0`
5. 填写发布说明（从CHANGELOG.md复制）
6. 上传构建的包（可选）
7. 点击"Publish release"

### 11. 合并发布分支

```bash
# 切换回main分支
git checkout main

# 合并发布分支
git merge release/v1.1.0

# 推送main分支
git push origin main

# 删除发布分支
git branch -d release/v1.1.0
git push origin --delete release/v1.1.0
```

## 发布检查清单

### 代码质量

- [ ] 所有测试通过
- [ ] 测试覆盖率 ≥ 80%
- [ ] 代码风格检查通过（flake8, black）
- [ ] 类型检查通过（mypy）
- [ ] 无已知关键Bug

### 文档完整性

- [ ] 变更日志已更新
- [ ] README已更新（如有需要）
- [ ] API文档已更新
- [ ] 用户指南已更新（如有新功能）
- [ ] 示例代码已更新

### 构建和打包

- [ ] 版本号已更新
- [ ] setup.py已更新
- [ ] 构建成功
- [ ] 包验证通过
- [ ] 安装测试通过

### 发布

- [ ] Git标签已创建
- [ ] 包已上传到PyPI
- [ ] GitHub Release已创建
- [ ] 发布公告已发送（如有邮件列表）

### 发布后

- [ ] 发布分支已合并
- [ ] 文档网站已更新
- [ ] 社区通知已发送
- [ ] 监控发布状态

## 发布后工作

### 1. 更新文档网站

如果项目有文档网站：

```bash
# 更新文档
git checkout gh-pages
git merge main
# 构建文档
mkdocs build
git add .
git commit -m "Update docs for v1.1.0"
git push origin gh-pages
```

### 2. 社区通知

- **GitHub Discussions**: 发布新版本公告
- **邮件列表**: 发送发布通知（如有）
- **社交媒体**: 分享发布信息（可选）

### 3. 监控发布状态

- [ ] 检查PyPI下载统计
- [ ] 监控GitHub Issues（是否有安装问题）
- [ ] 检查错误报告
- [ ] 收集用户反馈

### 4. 后续工作

- [ ] 更新路线图
- [ ] 规划下一个版本
- [ ] 处理用户反馈
- [ ] 修复发布后发现的Bug

## 回滚流程

### 如果发布出现问题

#### 1. 立即回滚PyPI

```bash
# 注意：PyPI不允许删除已发布的版本
# 只能发布新版本修复问题
```

#### 2. 发布修复版本

```bash
# 快速修复并发布补丁版本
# 例如：1.1.0 → 1.1.1
```

#### 3. 更新GitHub Release

- 在GitHub Release中添加已知问题说明
- 提供回滚或修复建议

#### 4. 通知用户

- 在GitHub Issues中发布公告
- 在文档中添加已知问题说明

## 自动化发布

### GitHub Actions工作流

创建 `.github/workflows/release.yml`:

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  build-and-publish:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2

      - name: Set up Python
        uses: actions/setup-python@v2
        with:
          python-version: '3.9'

      - name: Install dependencies
        run: |
          pip install build twine

      - name: Build package
        run: python -m build

      - name: Publish to PyPI
        env:
          TWINE_USERNAME: __token__
          TWINE_PASSWORD: ${{ secrets.PYPI_API_TOKEN }}
        run: twine upload dist/*
```

### 使用脚本自动化

创建 `scripts/release.sh`:

```bash
#!/bin/bash
set -e

VERSION=$1
if [ -z "$VERSION" ]; then
    echo "Usage: ./scripts/release.sh <version>"
    exit 1
fi

# 更新版本号
echo "__version__ = \"$VERSION\"" > algebraic_structures/__version__.py

# 运行测试
pytest

# 构建包
python -m build

# 创建标签
git tag -a "v$VERSION" -m "Release version $VERSION"
git push origin "v$VERSION"

# 发布到PyPI
twine upload dist/*
```

## 常见问题

### Q1: 如何确定版本号？

**A**: 根据语义化版本规范：
- **MAJOR**: API不兼容变更
- **MINOR**: 新功能（向后兼容）
- **PATCH**: Bug修复

### Q2: 发布前需要做什么？

**A**:
1. 确保所有测试通过
2. 更新变更日志
3. 更新版本号
4. 创建Git标签
5. 构建和测试包

### Q3: 如何回滚发布？

**A**: PyPI不允许删除已发布的版本，只能发布新的修复版本。

### Q4: 发布失败怎么办？

**A**:
1. 检查错误信息
2. 修复问题
3. 重新构建和发布
4. 如果问题严重，发布修复版本

### Q5: 如何处理预发布版本？

**A**: 使用预发布标签（alpha, beta, rc），例如 `1.1.0-alpha.1`。

## 发布时间表

### 常规发布周期

- **主版本**: 按需发布（重大变更）
- **次版本**: 每3-6个月
- **修订版本**: 按需发布（Bug修复）

### 发布计划示例

```
2025-01-15: v1.0.0 (初始发布)
2025-02-15: v1.0.1 (Bug修复)
2025-04-15: v1.1.0 (新功能)
2025-05-01: v1.1.1 (Bug修复)
2025-07-15: v1.2.0 (新功能)
2025-10-15: v2.0.0 (重大变更)
```

## 资源链接

- **[变更日志](00-Python实现-代数结构变更日志.md)**: 版本变更历史
- **[贡献指南](00-Python实现-代数结构贡献指南.md)**: 贡献流程
- **[测试指南](00-Python实现-代数结构测试指南.md)**: 测试要求
- **[路线图](00-Python实现-代数结构路线图.md)**: 未来规划

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组

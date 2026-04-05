---
title: 测试快速入门
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 测试快速入门

## 5分钟快速开始

### 1. 安装依赖

```bash
cd tests

# 前端测试依赖
npm install

# 后端测试依赖
cd backend
pip install -r requirements-test.txt
cd ..
```

### 2. 运行测试

```bash
# 运行所有测试
./run-tests.sh

# 或在Windows上
.\run-tests.ps1
```

### 3. 运行特定测试

```bash
# 仅前端测试
./run-tests.sh frontend

# 仅后端测试
./run-tests.sh backend

# 仅单元测试
./run-tests.sh unit

# 生成覆盖率报告
./run-tests.sh all --coverage
```

## 编写新测试

### 前端单元测试示例

```typescript
// tests/frontend/unit/components/MyComponent.test.tsx
import { render, screen } from '@testing-library/react';
import MyComponent from '@components/MyComponent';

describe('MyComponent', () => {
  it('应该正确渲染', () => {
    render(<MyComponent title="测试" />);
    expect(screen.getByText('测试')).toBeInTheDocument();
  });
});
```

### 后端单元测试示例

```python
# tests/backend/unit/test_my_module.py
import pytest

def test_my_function():
    """测试我的函数"""
    result = my_function(2, 3)
    assert result == 5

class TestMyClass:
    """测试我的类"""
    
    def test_method(self):
        """测试方法"""
        obj = MyClass()
        assert obj.method() == expected_value
```

### E2E测试示例

```typescript
// tests/frontend/e2e/specs/feature.cy.ts
describe('功能测试', () => {
  it('用户应该能完成某个功能', () => {
    cy.visit('/');
    cy.get('[data-testid="button"]').click();
    cy.get('[data-testid="result"]').should('contain', '成功');
  });
});
```

## 常用命令速查

| 命令 | 说明 |
|------|------|
| `npm run test:unit` | 运行前端单元测试 |
| `npm run test:unit:watch` | 监视模式运行测试 |
| `pytest` | 运行后端测试 |
| `pytest -v` | 详细输出 |
| `pytest -k "test_name"` | 运行特定测试 |
| `pytest --cov` | 生成覆盖率 |
| `lake test` | 运行Lean4测试 |
| `npx cypress open` | 打开Cypress交互界面 |

## 调试技巧

### 前端测试调试

```bash
# 单文件调试
npx jest --testPathPattern=MyComponent.test.tsx

# 调试模式
node --inspect-brk node_modules/.bin/jest --runInBand
```

### 后端测试调试

```bash
# 进入pdb调试
pytest --pdb

# 在失败处停止
pytest -x
```

### E2E测试调试

```bash
# 打开交互界面
npx cypress open

# 截图失败
# 自动保存到 tests/frontend/e2e/screenshots/
```

## 常见问题

### Q: 测试超时怎么办？
```bash
# 增加超时时间
npx jest --testTimeout=30000
pytest --timeout=60
```

### Q: 如何跳过某些测试？
```typescript
// 跳过测试
it.skip('跳过的测试', () => { ... });

// 仅运行此测试
it.only('唯一测试', () => { ... });
```

```python
# Python
@pytest.mark.skip(reason="暂时跳过")
def test_skipped(): ...

@pytest.mark.skipif(condition, reason="条件跳过")
def test_conditional(): ...
```

### Q: 如何模拟API？

```typescript
// 前端 - 使用MSW
import { rest } from 'msw';
import { setupServer } from 'msw/node';

const server = setupServer(
  rest.get('/api/concepts', (req, res, ctx) => {
    return res(ctx.json([{ id: '1', name: '测试' }]));
  })
);
```

```python
# 后端 - 使用responses
import responses

@responses.activate
def test_api():
    responses.add(
        responses.GET,
        'https://api.example.com/data[需更新]',
        json={'result': 'success'}
    )
```

## 下一步

- 阅读完整文档: [README.md](./README.md)
- 查看测试示例: [frontend/unit](./frontend/unit/)
- 了解CI/CD: [.github/workflows](../.github/workflows/)

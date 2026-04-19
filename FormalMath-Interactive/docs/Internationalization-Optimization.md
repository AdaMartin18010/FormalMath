---
title: 国际化UI/UX优化文档
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# 国际化UI/UX优化文档

## 概述

本文档描述了FormalMath项目的国际化UI/UX优化方案，包括RTL支持、文化适配、无障碍优化和性能优化。

## 1. RTL语言支持

### 支持的语言

- **LTR语言**: 英语(en)、中文(zh)、日语(ja)、韩语(ko)、西班牙语(es)、法语(fr)、德语(de)、俄语(ru)
- **RTL语言**: 阿拉伯语(ar)、希伯来语(he)

### 核心功能

#### useRTL Hook
```typescript
import { useRTL } from '@hooks/a11y';

function Component() {
  const { isRTL, direction, mirrorClass, flipClass } = useRTL();
  
  return (
    <div className={mirrorClass}>
      <Icon className={flipClass} />
    </div>
  );
}
```

#### RTL样式类
- `.rtl-flip` - 水平翻转元素
- `.rtl-rotate-arrow-right` - 旋转箭头方向
- `.rtl-ms-*` / `.rtl-me-*` - 逻辑边距
- `.rtl-ps-*` / `.rtl-pe-*` - 逻辑内边距

### 文件结构
```
src/
├── styles/
│   └── rtl.css              # RTL样式定义
├── i18n/
│   ├── config.ts            # i18n配置
│   └── locales/
│       ├── en.json          # 英语
│       ├── zh.json          # 中文
│       ├── ar.json          # 阿拉伯语
│       └── he.json          # 希伯来语
```

## 2. 文化适配

### CulturalProvider

提供文化上下文，包括：
- 文化区域检测（东亚、中东、西方）
- 紧凑模式（东亚语言）
- 数字格式（西方、阿拉伯-印度、东方阿拉伯）
- 日期格式

```typescript
import { CulturalProvider, CulturalDate, CulturalNumber } from '@components/Accessibility';

function App() {
  return (
    <CulturalProvider>
      <CulturalDate date={new Date()} format="long" />
      <CulturalNumber value={1234567.89} format="currency" currency="CNY" />
    </CulturalProvider>
  );
}
```

### 文化敏感组件

- **CulturalDate** - 本地化日期显示
- **CulturalNumber** - 本地化数字/货币显示
- **CulturalSpacing** - 根据文化调整间距
- **CulturalIcon** - 文化敏感图标

## 3. 无障碍优化 (WCAG 2.1)

### A级要求

#### 1. 键盘导航
```typescript
import { useFocusTrap, useFocusManager } from '@hooks/a11y';

// 焦点陷阱（模态框）
function Modal({ onClose }) {
  const containerRef = useFocusTrap({
    enabled: true,
    onEscape: onClose,
  });
  
  return <div ref={containerRef}>...</div>;
}
```

#### 2. 跳过链接
```tsx
import { SkipLink } from '@components/Accessibility';

<SkipLink targetId="main-content" />
<main id="main-content" tabIndex={-1}>
  {/* 主内容 */}
</main>
```

#### 3. 屏幕阅读器通知
```typescript
import { useAnnounce } from '@hooks/a11y';

function Component() {
  const { announce, announceSuccess, announceError } = useAnnounce();
  
  const handleAction = async () => {
    announceLoading('保存中...');
    try {
      await save();
      announceSuccess('保存成功');
    } catch (e) {
      announceError('保存失败');
    }
  };
}
```

### AA级要求

#### 1. 焦点可见性
```css
/* 键盘导航的焦点样式 */
*:focus-visible {
  outline: 3px solid #2563eb;
  outline-offset: 2px;
}
```

#### 2. 减少动画
```typescript
import { useReducedMotion } from '@hooks/a11y';

function AnimatedComponent() {
  const prefersReducedMotion = useReducedMotion();
  
  return (
    <motion.div
      animate={prefersReducedMotion ? {} : { opacity: 1 }}
    />
  );
}
```

#### 3. 高对比度模式
```tsx
import { HighContrastProvider, HighContrastToggle } from '@components/Accessibility';

<HighContrastProvider>
  <HighContrastToggle />
</HighContrastProvider>
```

### AAA级要求

#### 1. 增强对比度
- 文本对比度：7:1
- 大文本对比度：4.5:1

#### 2. 键盘无陷阱
- 所有功能可通过键盘访问
- 焦点顺序逻辑合理

## 4. 性能优化

### 懒加载

```typescript
import { lazyLoad, createLazyComponent } from '@utils/performance';

// 基本懒加载
const HeavyComponent = lazyLoad(
  () => import('./HeavyComponent'),
  { timeout: 10000, retries: 2 }
);

// 可预加载的懒加载
const { Component, preload } = createLazyComponent(
  () => import('./HeavyComponent')
);

// 鼠标悬停时预加载
<button onMouseEnter={preload}>悬停预加载</button>
```

### 缓存

```typescript
import { LRUCache, withCache } from '@utils/performance';

// LRU缓存
const cache = new LRUCache<string>({
  ttl: 5 * 60 * 1000,  // 5分钟
  maxSize: 100,
});

// 函数缓存
const getExpensiveData = withCache(
  async (id: string) => {
    return await fetchData(id);
  },
  { ttl: 60000 }
);
```

### 虚拟列表

```typescript
import { calculateVirtualRange } from '@utils/performance';

function VirtualList({ items, itemHeight, containerHeight }) {
  const [scrollTop, setScrollTop] = useState(0);
  
  const { startIndex, endIndex, startOffset, totalHeight } = 
    calculateVirtualRange(scrollTop, items.length, {
      itemHeight,
      containerHeight,
      overscan: 3,
    });
  
  const visibleItems = items.slice(startIndex, endIndex + 1);
  
  return (
    <div style={{ height: containerHeight, overflow: 'auto' }}>
      <div style={{ height: totalHeight }}>
        <div style={{ transform: `translateY(${startOffset}px)` }}>
          {visibleItems.map(item => <Item key={item.id} {...item} />)}
        </div>
      </div>
    </div>
  );
}
```

## 5. A/B测试

### 基础使用

```typescript
import { useABTest } from '@utils/ab-testing';

function Homepage() {
  const { variant, config, track, isControl } = useABTest('homepage_layout');
  
  useEffect(() => {
    track('view');
  }, []);
  
  return (
    <div>
      {variant === 'variant_a' && <CardLayout onClick={() => track('click')} />}
      {variant === 'variant_b' && <ListLayout onClick={() => track('click')} />}
    </div>
  );
}
```

### 组件变体

```typescript
import { useABTestVariant } from '@utils/ab-testing';

function Button({ children }) {
  const { Component, track } = useABTestVariant('button_color', {
    control: BlueButton,
    variant_green: GreenButton,
    variant_red: RedButton,
  });
  
  return <Component onClick={() => track('click')}>{children}</Component>;
}
```

### 实验配置

```typescript
// config.ts
export const experiments = {
  homepage_layout: {
    id: 'homepage_layout',
    name: '首页布局优化',
    variants: [
      { id: 'control', name: '原始布局', weight: 0.5 },
      { id: 'variant_a', name: '卡片式', weight: 0.25 },
      { id: 'variant_b', name: '列表式', weight: 0.25 },
    ],
    goals: ['engagement', 'conversion'],
  },
};
```

## 6. 语言切换器

```tsx
import { LanguageSwitcher } from '@components/Accessibility';

// 下拉菜单样式
<LanguageSwitcher variant="dropdown" showFlags />

// 内联样式
<LanguageSwitcher variant="inline" />

// 极简样式
<LanguageSwitcher variant="minimal" />

// 移动端紧凑样式
<CompactLanguageSwitcher />
```

## 7. 集成示例

### 完整的App集成

```tsx
import { I18nextProvider } from 'react-i18next';
import i18n from '@i18n/config';
import { CulturalProvider } from '@components/Accessibility';
import { HighContrastProvider } from '@components/Accessibility';
import { SkipLink, LanguageSwitcher } from '@components/Accessibility';

function App() {
  return (
    <I18nextProvider i18n={i18n}>
      <CulturalProvider>
        <HighContrastProvider>
          <SkipLink targetId="main-content" />
          <header>
            <LanguageSwitcher variant="dropdown" />
            {/* 其他头部内容 */}
          </header>
          <main id="main-content" tabIndex={-1}>
            {/* 主内容 */}
          </main>
        </HighContrastProvider>
      </CulturalProvider>
    </I18nextProvider>
  );
}
```

## 8. 测试清单

### RTL测试
- [ ] 阿拉伯语文本正确显示为RTL
- [ ] 希伯来语文本正确显示为RTL
- [ ] 图标在RTL模式下正确翻转
- [ ] 导航方向在RTL模式下正确
- [ ] 布局在LTR和RTL间正确切换

### 无障碍测试
- [ ] 所有功能可通过键盘访问
- [ ] 焦点顺序逻辑合理
- [ ] 焦点样式清晰可见
- [ ] 屏幕阅读器正确读取内容
- [ ] 颜色对比度符合WCAG AA标准
- [ ] 减少动画偏好被尊重

### 性能测试
- [ ] 组件懒加载正常工作
- [ ] 缓存命中率高
- [ ] 虚拟列表滚动流畅
- [ ] 首屏加载时间 < 3秒

### A/B测试
- [ ] 用户正确分配到变体
- [ ] 事件正确追踪
- [ ] 实验配置可动态更新

## 9. 依赖项

```json
{
  "dependencies": {
    "i18next": "^23.0.0",
    "react-i18next": "^13.0.0",
    "i18next-browser-languagedetector": "^7.0.0",
    "uuid": "^9.0.0"
  }
}
```

## 10. 后续优化建议

1. **更多语言支持**: 添加印地语、葡萄牙语等
2. **语音输入支持**: 集成语音识别API
3. **个性化推荐**: 基于用户行为的文化偏好学习
4. **自动化测试**: 添加RTL和无障碍的自动化测试
5. **性能监控**: 集成RUM（真实用户监控）工具

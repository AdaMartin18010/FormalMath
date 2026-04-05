---
title: SocialFeatures 社交功能模块
msc_primary: 00A99
processed_at: '2026-04-05'
---
# SocialFeatures 社交功能模块

FormalMath Interactive 的社交媒体集成模块，提供完整的社交分享、登录和嵌入功能。

## 功能特性

- ✅ **社交分享按钮** - 支持 Twitter、Facebook、LinkedIn、微博、微信等
- ✅ **Open Graph 标签** - 完整的 SEO 元数据支持
- ✅ **Twitter Cards** - 支持摘要卡和大图卡
- ✅ **社交登录** - GitHub、Google、Twitter、LinkedIn、微信、微博、Apple
- ✅ **内容嵌入** - 生成 iframe 嵌入代码，支持 oEmbed 标准
- ✅ **分享统计** - 获取内容在各平台的分享数据
- ✅ **浮动分享按钮** - 页面右下角悬浮分享按钮
- ✅ **响应式设计** - 适配移动端和桌面端

## 组件列表

### 分享组件

| 组件 | 说明 |
|------|------|
| `ShareButtons` | 基础分享按钮组 |
| `FloatingShareButton` | 浮动分享按钮 |
| `InlineShareButtons` | 内联分享按钮（带点赞/收藏） |
| `SocialShare` | 分享弹窗组件 |

### 元数据组件

| 组件 | 说明 |
|------|------|
| `OpenGraphMeta` | Open Graph / Twitter Cards 元数据 |
| `useSocialMeta` | 社交元数据 Hook |
| `useShareCount` | 分享计数 Hook |

### 登录组件

| 组件 | 说明 |
|------|------|
| `SocialLogin` | 社交账号登录 |
| `SocialLink` | 账号绑定管理 |

### 嵌入组件

| 组件 | 说明 |
|------|------|
| `ContentEmbed` | 内容嵌入配置器 |
| `EmbedViewer` | 嵌入内容查看器 |

## 快速开始

```tsx
import { 
  ShareButtons, 
  OpenGraphMeta,
  SocialLogin 
} from './components/SocialFeatures';

function MyPage() {
  return (
    <>
      <OpenGraphMeta
        title="页面标题"
        description="页面描述"
        url="https://example.com/page"
        image="/preview.png"
      />
      
      <ShareButtons
        url={window.location.href}
        title="分享标题"
        platforms={['twitter', 'facebook', 'copy']}
      />
      
      <SocialLogin
        providers={['github', 'google']}
        onSuccess={(user, provider) => console.log(user)}
      />
    </>
  );
}
```

## 文件结构

```
SocialFeatures/
├── OpenGraphMeta.tsx      # Open Graph 元数据组件
├── SocialShare.tsx        # 分享弹窗组件
├── ShareButtons.tsx       # 分享按钮组
├── SocialLogin.tsx        # 社交登录
├── ContentEmbed.tsx       # 内容嵌入
├── useSocialMeta.ts       # 社交元数据 Hook
├── index.ts               # 模块导出
├── examples/              # 示例代码
│   └── SocialFeaturesExample.tsx
└── README.md              # 本文件
```

## 依赖

- `react-helmet-async`: 管理文档 head 中的 meta 标签

## 详细文档

查看完整文档：[Social-Media-Integration.md](../../../docs/Social-Media-Integration.md)

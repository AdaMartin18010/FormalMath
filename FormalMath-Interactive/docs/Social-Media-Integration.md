---
title: 社交媒体集成指南
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# 社交媒体集成指南

本文档介绍 FormalMath Interactive 的社交媒体集成功能，包括社交分享、Open Graph 标签、Twitter Cards、社交登录和内容嵌入。

## 目录

1. [快速开始](#快速开始)
2. [社交分享组件](#社交分享组件)
3. [Open Graph 和 Twitter Cards](#open-graph-和-twitter-cards)
4. [社交登录](#社交登录)
5. [内容嵌入](#内容嵌入)
6. [环境配置](#环境配置)
7. [API 参考](#api-参考)

## 快速开始

### 1. 安装依赖

```bash
cd FormalMath-Interactive
npm install
```

依赖已包含在 `package.json` 中：
- `react-helmet-async`: 用于管理文档 head 中的 meta 标签

### 2. 在应用中添加 HelmetProvider

```tsx
// src/main.tsx
import { HelmetProvider } from 'react-helmet-async';

ReactDOM.createRoot(document.getElementById('root')!).render(
  <HelmetProvider>
    <App />
  </HelmetProvider>
);
```

### 3. 使用社交组件

```tsx
import { 
  ShareButtons, 
  OpenGraphMeta, 
  SocialLogin,
  useSocialMeta 
} from './components/SocialFeatures';
```

## 社交分享组件

### ShareButtons - 分享按钮组

基础用法：

```tsx
import { ShareButtons } from './components/SocialFeatures';

function ConceptPage() {
  return (
    <ShareButtons
      url="https://formalmath.example.com/concept/algebra[需更新]"
      title="代数 - FormalMath"
      description="学习代数的基本概念"
      hashtags={['数学', '代数', 'FormalMath']}
      platforms={['twitter', 'facebook', 'linkedin', 'weibo', 'copy']}
      onShare={(platform) => console.log(`Shared to ${platform}`)}
    />
  );
}
```

### FloatingShareButton - 浮动分享按钮

```tsx
import { FloatingShareButton } from './components/SocialFeatures';

function ArticlePage() {
  return (
    <>
      {/* 页面内容 */}
      <FloatingShareButton
        url={window.location.href}
        title="文章标题"
        description="文章描述"
        position="bottom-right"
        offset={{ x: 24, y: 24 }}
      />
    </>
  );
}
```

### InlineShareButtons - 内联分享按钮（带统计）

```tsx
import { InlineShareButtons } from './components/SocialFeatures';

function ContentPage() {
  return (
    <InlineShareButtons
      url={window.location.href}
      title="内容标题"
      likes={128}
      views={1024}
      bookmarks={32}
      isLiked={false}
      isBookmarked={false}
      onLike={() => console.log('Liked')}
      onBookmark={() => console.log('Bookmarked')}
    />
  );
}
```

### SocialShare - 分享弹窗

```tsx
import { SocialShare } from './components/SocialFeatures';

function ShareModal() {
  const [isOpen, setIsOpen] = useState(false);

  return (
    <>
      <button onClick={() => setIsOpen(true)}>分享</button>
      {isOpen && (
        <div className="fixed inset-0 z-50 flex items-center justify-center bg-black/50">
          <SocialShare
            data={{
              title: '代数概念',
              description: '学习代数的基本概念和定理',
              url: window.location.href,
              image: '/images/algebra-preview.png',
            }}
            platforms={['wechat', 'weibo', 'twitter', 'copy', 'qrcode']}
            onClose={() => setIsOpen(false)}
          />
        </div>
      )}
    </>
  );
}
```

## Open Graph 和 Twitter Cards

### OpenGraphMeta - SEO 元数据组件

```tsx
import { OpenGraphMeta } from './components/SocialFeatures';

function ConceptPage({ concept }) {
  return (
    <>
      <OpenGraphMeta
        title={concept.name}
        description={concept.description}
        url={`https://formalmath.example.com/concept/${concept.id}[需更新]`}
        image={concept.image}
        imageWidth={1200}
        imageHeight={630}
        type="article"
        keywords={['数学', '代数', concept.name]}
        author="FormalMath Team"
        publishedTime={concept.createdAt}
        modifiedTime={concept.updatedAt}
        section="数学概念"
        tags={['代数', '基础数学']}
        twitterCard="summary_large_image"
        twitterSite="@formalmath"
        twitterCreator="@author"
      />
      {/* 页面内容 */}
    </>
  );
}
```

### 使用 useSocialMeta Hook

```tsx
import { useSocialMeta } from './components/SocialFeatures';

function ConceptPage({ concept }) {
  const { share, generateShareUrl } = useSocialMeta({
    title: concept.name,
    description: concept.description,
    url: `https://formalmath.example.com/concept/${concept.id}[需更新]`,
    image: concept.image,
    type: 'article',
    keywords: ['数学', '代数'],
    updateDocument: true, // 自动更新文档 meta 标签
  });

  return (
    <div>
      <h1>{concept.name}</h1>
      <button onClick={() => share('twitter')}>分享到 Twitter</button>
      <button onClick={() => share('native')}>原生分享</button>
    </div>
  );
}
```

### 预定义元数据配置

```tsx
import { mathContentMeta, generateConceptMeta } from './components/SocialFeatures';

// 使用预定义配置
const conceptMeta = {
  ...mathContentMeta.concept,
  title: '代数',
  description: '代数的基本概念',
};

// 自动生成概念页面元数据
const meta = generateConceptMeta(
  {
    name: '代数',
    description: '代数的基本概念',
    id: 'algebra',
    category: '基础数学',
    image: '/images/algebra.png',
  },
  'https://formalmath.example.com[需更新]'
);
```

## 社交登录

### SocialLogin - 社交账号登录

```tsx
import { SocialLogin } from './components/SocialFeatures';

function LoginPage() {
  return (
    <SocialLogin
      providers={['github', 'google', 'twitter', 'wechat']}
      onSuccess={(user, provider) => {
        console.log('Login success:', user);
        // 处理登录成功
      }}
      onError={(error, provider) => {
        console.error('Login error:', error);
        // 处理登录错误
      }}
    />
  );
}
```

### SocialLink - 账号绑定

```tsx
import { SocialLink } from './components/SocialFeatures';

function SettingsPage() {
  const [linkedAccounts, setLinkedAccounts] = useState([]);

  return (
    <SocialLink
      linkedAccounts={linkedAccounts}
      availableProviders={['github', 'google', 'twitter']}
      onLink={(user, provider) => {
        setLinkedAccounts([...linkedAccounts, user]);
      }}
      onUnlink={(provider) => {
        setLinkedAccounts(linkedAccounts.filter(a => a.provider !== provider));
      }}
    />
  );
}
```

## 内容嵌入

### ContentEmbed - 内容嵌入组件

```tsx
import { ContentEmbed } from './components/SocialFeatures';

function SharePage() {
  return (
    <ContentEmbed
      url="https://formalmath.example.com/concept/algebra[需更新]"
      title="代数概念"
      description="学习代数的基本概念"
      thumbnail="/images/algebra-thumb.png"
      config={{
        size: 'responsive',
        theme: 'auto',
        showHeader: true,
        allowFullscreen: true,
        borderRadius: 8,
      }}
      onConfigChange={(config) => console.log('Config changed:', config)}
    />
  );
}
```

### EmbedViewer - 嵌入内容查看器

在 iframe 嵌入页面中使用：

```tsx
import { EmbedViewer } from './components/SocialFeatures';

function EmbedPage() {
  return (
    <EmbedViewer
      title="代数概念"
      showHeader={true}
      showFooter={true}
      theme="auto"
      allowInteraction={true}
    >
      {/* 嵌入的内容 */}
      <ConceptContent />
    </EmbedViewer>
  );
}
```

### oEmbed API

支持 oEmbed 标准，可与其他平台集成：

```
GET /oembed?url={encoded_url}&format=json&maxwidth=800&maxheight=600
```

响应示例：

```json
{
  "type": "rich",
  "version": "1.0",
  "title": "代数概念",
  "author_name": "FormalMath",
  "author_url": "https://formalmath.example.com[需更新]",
  "provider_name": "FormalMath",
  "provider_url": "https://formalmath.example.com[需更新]",
  "html": "<iframe...></iframe>",
  "width": 800,
  "height": 600
}
```

## 环境配置

### 环境变量

创建 `.env` 文件：

```env
# 社交登录配置
VITE_GITHUB_CLIENT_ID=your_github_client_id
VITE_GOOGLE_CLIENT_ID=your_google_client_id
VITE_TWITTER_CLIENT_ID=your_twitter_client_id
VITE_LINKEDIN_CLIENT_ID=your_linkedin_client_id
VITE_WECHAT_APP_ID=your_wechat_app_id
VITE_WEIBO_CLIENT_ID=your_weibo_client_id
VITE_APPLE_CLIENT_ID=your_apple_client_id

# 站点配置
VITE_SITE_URL=https://formalmath.example.com[需更新]
VITE_SITE_NAME=FormalMath
VITE_TWITTER_HANDLE=@formalmath
```

### OAuth 回调路由

配置 OAuth 回调路由：

```tsx
// App.tsx
<Routes>
  <Route path="/auth/callback/:provider" element={<OAuthCallback />} />
</Routes>
```

创建回调处理组件：

```tsx
// components/OAuthCallback.tsx
import { useEffect } from 'react';
import { useParams, useSearchParams } from 'react-router-dom';

function OAuthCallback() {
  const { provider } = useParams();
  const [searchParams] = useSearchParams();

  useEffect(() => {
    const code = searchParams.get('code');
    const state = searchParams.get('state');
    const error = searchParams.get('error');

    if (error) {
      window.opener?.postMessage({
        type: 'oauth:error',
        error: { code: error, message: searchParams.get('error_description') },
      }, window.location.origin);
    } else if (code) {
      // 交换 access token
      fetch('/api/auth/callback', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ code, provider, state }),
      })
      .then(res => res.json())
      .then(data => {
        window.opener?.postMessage({
          type: 'oauth:success',
          data,
        }, window.location.origin);
      });
    }

    window.close();
  }, []);

  return <div>处理登录中...</div>;
}
```

## API 参考

### ShareButtons Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| url | string | 必填 | 分享链接 |
| title | string | 必填 | 分享标题 |
| description | string | - | 分享描述 |
| image | string | - | 分享图片 |
| hashtags | string[] | [] | 话题标签 |
| via | string | - | Twitter 提及 |
| platforms | ShareButtonPlatform[] | ['twitter', 'facebook', 'linkedin', 'copy'] | 启用的平台 |
| onShare | (platform) => void | - | 分享回调 |
| variant | 'default' \| 'minimal' \| 'pill' | 'default' | 按钮样式 |
| size | 'sm' \| 'md' \| 'lg' | 'md' | 按钮大小 |
| showCount | boolean | false | 显示分享数 |

### OpenGraphMeta Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| title | string | 必填 | 页面标题 |
| description | string | 必填 | 页面描述 |
| url | string | - | 页面 URL |
| image | string | - | 分享图片 |
| type | 'website' \| 'article' \| 'profile' | 'website' | 页面类型 |
| keywords | string[] | [] | 关键词 |
| author | string | - | 作者 |
| publishedTime | string | - | 发布时间 |
| modifiedTime | string | - | 修改时间 |
| twitterCard | 'summary' \| 'summary_large_image' | 'summary_large_image' | Twitter 卡片类型 |

### SocialLogin Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| providers | SocialProvider[] | ['github', 'google'] | 启用的登录方式 |
| onSuccess | (user, provider) => void | - | 登录成功回调 |
| onError | (error, provider) => void | - | 登录失败回调 |

### ContentEmbed Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| url | string | 必填 | 嵌入内容 URL |
| title | string | 必填 | 标题 |
| config | Partial<EmbedConfig> | - | 嵌入配置 |
| onConfigChange | (config) => void | - | 配置变更回调 |

### useSocialMeta Options

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| title | string | 必填 | 页面标题 |
| description | string | 必填 | 页面描述 |
| url | string | - | 页面 URL |
| image | string | - | 分享图片 |
| type | 'website' \| 'article' | 'website' | 页面类型 |
| updateDocument | boolean | true | 是否更新文档 meta |

### useShareCount

```tsx
const { counts, loading, error, refresh } = useShareCount(
  'https://example.com/page[需更新]',
  ['facebook', 'pinterest']
);

// counts: { facebook: 42, pinterest: 15 }
```

## 注意事项

1. **图片尺寸**: Open Graph 图片推荐尺寸为 1200x630 像素
2. **Twitter Cards**: 需要验证 Twitter 账号并申请白名单
3. **微信分享**: 需要使用微信 JS-SDK 实现完整功能
4. **OAuth 配置**: 在各平台开发者控制台配置回调 URL
5. **CORS**: 确保嵌入 API 端点支持跨域访问

## 示例

完整示例请查看 `src/components/SocialFeatures/examples/` 目录。

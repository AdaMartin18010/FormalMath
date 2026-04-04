import React from 'react';
import { Helmet } from 'react-helmet-async';

export interface OpenGraphMetaProps {
  title: string;
  description: string;
  url: string;
  image?: string;
  imageWidth?: number;
  imageHeight?: number;
  imageAlt?: string;
  type?: 'website' | 'article' | 'profile';
  siteName?: string;
  locale?: string;
  keywords?: string[];
  author?: string;
  publishedTime?: string;
  modifiedTime?: string;
  section?: string;
  tags?: string[];
  twitterCard?: 'summary' | 'summary_large_image' | 'app' | 'player';
  twitterSite?: string;
  twitterCreator?: string;
  twitterImage?: string;
  facebookAppId?: string;
  facebookAdmins?: string[];
}

export const OpenGraphMeta: React.FC<OpenGraphMetaProps> = ({
  title,
  description,
  url,
  image,
  imageWidth = 1200,
  imageHeight = 630,
  imageAlt,
  type = 'website',
  siteName = 'FormalMath',
  locale = 'zh_CN',
  keywords = [],
  author,
  publishedTime,
  modifiedTime,
  section,
  tags = [],
  twitterCard = 'summary_large_image',
  twitterSite = '@formalmath',
  twitterCreator,
  twitterImage,
  facebookAppId,
  facebookAdmins = [],
}) => {
  const fullTitle = `${title} | ${siteName}`;
  const safeDescription = description.slice(0, 200);

  return (
    <Helmet prioritizeSeoTags>
      {/* Basic Meta Tags */}
      <title>{fullTitle}</title>
      <meta name="description" content={safeDescription} />
      {keywords.length > 0 && (
        <meta name="keywords" content={keywords.join(', ')} />
      )}
      {author && <meta name="author" content={author} />}
      
      {/* Open Graph Meta Tags */}
      <meta property="og:title" content={title} />
      <meta property="og:description" content={safeDescription} />
      <meta property="og:url" content={url} />
      <meta property="og:type" content={type} />
      <meta property="og:site_name" content={siteName} />
      <meta property="og:locale" content={locale} />
      
      {/* Open Graph Image */}
      {image && (
        <>
          <meta property="og:image" content={image} />
          <meta property="og:image:width" content={String(imageWidth)} />
          <meta property="og:image:height" content={String(imageHeight)} />
          {imageAlt && <meta property="og:image:alt" content={imageAlt} />}
        </>
      )}
      
      {/* Article Specific */}
      {type === 'article' && (
        <>
          {publishedTime && (
            <meta property="article:published_time" content={publishedTime} />
          )}
          {modifiedTime && (
            <meta property="article:modified_time" content={modifiedTime} />
          )}
          {section && <meta property="article:section" content={section} />}
          {tags.map((tag, index) => (
            <meta key={index} property="article:tag" content={tag} />
          ))}
          {author && <meta property="article:author" content={author} />}
        </>
      )}
      
      {/* Profile Specific */}
      {type === 'profile' && (
        <>
          {author && (
            <>
              <meta property="profile:first_name" content={author.split(' ')[0]} />
              <meta property="profile:last_name" content={author.split(' ').slice(1).join(' ')} />
            </>
          )}
        </>
      )}
      
      {/* Twitter Cards */}
      <meta name="twitter:card" content={twitterCard} />
      <meta name="twitter:site" content={twitterSite} />
      <meta name="twitter:title" content={title} />
      <meta name="twitter:description" content={safeDescription} />
      {twitterCreator && <meta name="twitter:creator" content={twitterCreator} />}
      {(twitterImage || image) && (
        <meta name="twitter:image" content={twitterImage || image} />
      )}
      {imageAlt && (
        <meta name="twitter:image:alt" content={imageAlt} />
      )}
      
      {/* Facebook */}
      {facebookAppId && (
        <meta property="fb:app_id" content={facebookAppId} />
      )}
      {facebookAdmins.map((admin, index) => (
        <meta key={index} property="fb:admins" content={admin} />
      ))}
      
      {/* LinkedIn */}
      <meta property="linkedin:owner" content={twitterSite} />
      
      {/* WeChat (using QQ/WeChat specific) */}
      <meta itemProp="name" content={title} />
      <meta itemProp="description" content={safeDescription} />
      {image && <meta itemProp="image" content={image} />}
      
      {/* WhatsApp */}
      <meta property="og:image:secure_url" content={image} />
      
      {/* Pinterest */}
      <meta name="pinterest-rich-pin" content="true" />
      
      {/* Telegram */}
      <meta name="telegram:channel" content={twitterSite} />
    </Helmet>
  );
};

// 预定义的数学内容元数据配置
export const mathContentMeta = {
  // 数学概念页面默认配置
  concept: {
    type: 'article' as const,
    section: '数学概念',
    keywords: ['数学', '形式化数学', '数学概念', '数学知识图谱'],
  },
  // 证明助手页面默认配置
  proofAssistant: {
    type: 'article' as const,
    section: '形式化证明',
    keywords: ['形式化证明', 'Lean', '数学证明', '定理证明'],
  },
  // 学习路径页面默认配置
  learningPath: {
    type: 'website' as const,
    section: '学习路径',
    keywords: ['数学学习', '学习路径', '知识图谱', '个性化学习'],
  },
  // 游戏化页面默认配置
  gamification: {
    type: 'website' as const,
    section: '数学游戏',
    keywords: ['数学游戏', '数学挑战', '学习游戏', '数学趣味'],
  },
  // 协作页面默认配置
  collaboration: {
    type: 'website' as const,
    section: '协作学习',
    keywords: ['协作学习', '数学协作', '在线学习', '小组学习'],
  },
};

// 生成概念页面的元数据
export const generateConceptMeta = (
  concept: {
    name: string;
    description: string;
    id: string;
    category?: string;
    image?: string;
  },
  baseUrl: string
): OpenGraphMetaProps => ({
  title: concept.name,
  description: concept.description,
  url: `${baseUrl}/concept/${concept.id}`,
  image: concept.image,
  type: 'article',
  keywords: [...mathContentMeta.concept.keywords, concept.name, concept.category].filter(Boolean),
  section: mathContentMeta.concept.section,
  tags: [concept.category].filter(Boolean) as string[],
});

// 生成知识图谱页面的元数据
export const generateGraphMeta = (
  graph: {
    name: string;
    description: string;
    nodeCount: number;
    edgeCount: number;
  },
  baseUrl: string
): OpenGraphMetaProps => ({
  title: `${graph.name} - 知识图谱`,
  description: `${graph.description} | 包含 ${graph.nodeCount} 个概念和 ${graph.edgeCount} 条关系`,
  url: `${baseUrl}/graph`,
  type: 'website',
  keywords: ['知识图谱', '数学图谱', '概念关系', '数学知识', ...mathContentMeta.concept.keywords],
});

export default OpenGraphMeta;

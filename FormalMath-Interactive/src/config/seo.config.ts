/**
 * SEO Configuration for FormalMath Interactive
 * 搜索引擎优化配置
 */

export interface SEOMeta {
  title: string;
  description: string;
  keywords: string[];
  ogTitle?: string;
  ogDescription?: string;
  ogImage?: string;
  ogType?: string;
  twitterCard?: string;
  twitterTitle?: string;
  twitterDescription?: string;
  twitterImage?: string;
  canonicalUrl?: string;
  alternateLanguages?: Record<string, string>;
  noIndex?: boolean;
  noFollow?: boolean;
  structuredData?: object;
}

export interface PageSEO {
  [key: string]: SEOMeta;
}

// 默认SEO配置
export const defaultSEO: SEOMeta = {
  title: 'FormalMath Interactive - 交互式数学可视化平台',
  description: 'FormalMath是一个现代化的数学知识图谱可视化平台，提供交互式数学概念探索、推理树可视化、证明助手等功能，助力数学学习与教学。',
  keywords: [
    '数学可视化',
    '知识图谱',
    '数学教育',
    '交互式学习',
    '数学证明',
    'FormalMath',
    '数学概念',
    '数学推理',
    '数学工具',
    '在线教育',
  ],
  ogTitle: 'FormalMath Interactive - 交互式数学可视化平台',
  ogDescription: '探索数学之美，可视化数学知识图谱，交互式学习体验',
  ogImage: '/FormalMath/images/og-image.png',
  ogType: 'website',
  twitterCard: 'summary_large_image',
  twitterTitle: 'FormalMath Interactive - 交互式数学可视化平台',
  twitterDescription: '探索数学之美，可视化数学知识图谱',
  twitterImage: '/FormalMath/images/twitter-image.png',
  canonicalUrl: 'https://formalmath.example.com',
  alternateLanguages: {
    'zh-CN': 'https://formalmath.example.com',
    'en': 'https://formalmath.example.com/en',
    'ja': 'https://formalmath.example.com/ja',
  },
};

// 各页面SEO配置
export const pageSEO: PageSEO = {
  home: {
    title: 'FormalMath Interactive - 交互式数学可视化平台',
    description: 'FormalMath是一个现代化的数学知识图谱可视化平台，提供交互式数学概念探索、推理树可视化、证明助手等功能，助力数学学习与教学。',
    keywords: [
      '数学可视化',
      '知识图谱',
      '数学教育',
      '交互式学习',
      '数学证明',
      'FormalMath',
    ],
    ogType: 'website',
  },
  'knowledge-graph': {
    title: '数学知识图谱 - FormalMath Interactive',
    description: '交互式数学知识图谱可视化，探索数学概念之间的关联与层次结构，支持缩放、筛选和详细查看。',
    keywords: [
      '数学知识图谱',
      '概念可视化',
      '数学概念关系',
      'D3可视化',
      '图数据库',
    ],
    ogType: 'website',
  },
  'reasoning-tree': {
    title: '推理树可视化 - FormalMath Interactive',
    description: '数学推理过程的树形可视化，清晰展示证明步骤和逻辑推导链条，助力理解数学证明结构。',
    keywords: [
      '推理树',
      '数学证明',
      '逻辑推导',
      '证明可视化',
      '数学推理',
    ],
    ogType: 'website',
  },
  'mind-map': {
    title: '数学思维导图 - FormalMath Interactive',
    description: '数学概念的思维导图展示，以直观方式组织数学知识体系，支持多层级展开浏览。',
    keywords: [
      '数学思维导图',
      '知识组织',
      '概念地图',
      '学习工具',
    ],
    ogType: 'website',
  },
  comparison: {
    title: '概念对比分析 - FormalMath Interactive',
    description: '数学概念对比工具，并排比较不同概念的定义、性质和应用场景，深化理解差异。',
    keywords: [
      '概念对比',
      '数学概念分析',
      '差异比较',
      '学习工具',
    ],
    ogType: 'website',
  },
  'decision-tree': {
    title: '决策树可视化 - FormalMath Interactive',
    description: '数学问题求解的决策树展示，指导用户一步步解决数学问题，培养解题思维。',
    keywords: [
      '决策树',
      '问题求解',
      '数学解题',
      '交互式引导',
    ],
    ogType: 'website',
  },
  evolution: {
    title: '概念演化历史 - FormalMath Interactive',
    description: '数学概念的历史演化时间线，追溯概念的发展过程和里程碑事件，了解数学史。',
    keywords: [
      '数学史',
      '概念演化',
      '时间线',
      '数学发展',
    ],
    ogType: 'website',
  },
  analytics: {
    title: '学习数据分析 - FormalMath Interactive',
    description: '个性化学习数据分析仪表板，追踪学习进度、知识掌握情况和薄弱环节。',
    keywords: [
      '学习分析',
      '数据仪表板',
      '进度追踪',
      '个性化学习',
    ],
    ogType: 'website',
  },
  'proof-assistant': {
    title: 'Lean证明助手 - FormalMath Interactive',
    description: '在线Lean定理证明助手，支持交互式数学证明编写、验证和学习，集成AI辅助功能。',
    keywords: [
      'Lean证明',
      '定理证明',
      '形式化数学',
      '数学证明助手',
      'Lean4',
    ],
    ogType: 'website',
  },
  'visualization-gallery': {
    title: '可视化组件库 - FormalMath Interactive',
    description: 'FormalMath可视化组件展示，包括2D/3D图形、热力图、矩阵表等多种数学可视化组件。',
    keywords: [
      '可视化组件',
      '数学图形',
      'D3.js',
      'Three.js',
      '数据可视化',
    ],
    ogType: 'website',
  },
};

// 获取指定页面的SEO配置
export function getPageSEO(pageKey: string, locale: string = 'zh-CN'): SEOMeta {
  const pageConfig = pageSEO[pageKey] || {};
  return {
    ...defaultSEO,
    ...pageConfig,
    // 根据语言调整标题
    title: locale === 'en' 
      ? pageConfig.title?.replace('FormalMath Interactive', 'FormalMath Interactive').replace('数学', 'Mathematics ')
      : pageConfig.title,
  };
}

// Breadcrumb配置
export interface BreadcrumbItem {
  name: string;
  url: string;
  position: number;
}

export const breadcrumbs: Record<string, BreadcrumbItem[]> = {
  home: [{ name: '首页', url: '/', position: 1 }],
  'knowledge-graph': [
    { name: '首页', url: '/', position: 1 },
    { name: '知识图谱', url: '/knowledge-graph', position: 2 },
  ],
  'reasoning-tree': [
    { name: '首页', url: '/', position: 1 },
    { name: '推理树', url: '/reasoning-tree', position: 2 },
  ],
  'mind-map': [
    { name: '首页', url: '/', position: 1 },
    { name: '思维导图', url: '/mind-map', position: 2 },
  ],
  comparison: [
    { name: '首页', url: '/', position: 1 },
    { name: '对比分析', url: '/comparison', position: 2 },
  ],
  'decision-tree': [
    { name: '首页', url: '/', position: 1 },
    { name: '决策树', url: '/decision-tree', position: 2 },
  ],
  evolution: [
    { name: '首页', url: '/', position: 1 },
    { name: '演化历史', url: '/evolution', position: 2 },
  ],
  analytics: [
    { name: '首页', url: '/', position: 1 },
    { name: '数据分析', url: '/analytics', position: 2 },
  ],
  'proof-assistant': [
    { name: '首页', url: '/', position: 1 },
    { name: '证明助手', url: '/proof-assistant', position: 2 },
  ],
  'visualization-gallery': [
    { name: '首页', url: '/', position: 1 },
    { name: '可视化库', url: '/visualization-gallery', position: 2 },
  ],
};

// 生成BreadcrumbList结构化数据
export function generateBreadcrumbStructuredData(
  pageKey: string,
  baseUrl: string = 'https://formalmath.example.com'
): object | null {
  const items = breadcrumbs[pageKey];
  if (!items) return null;

  return {
    '@context': 'https://schema.org',
    '@type': 'BreadcrumbList',
    itemListElement: items.map((item) => ({
      '@type': 'ListItem',
      position: item.position,
      name: item.name,
      item: `${baseUrl}${item.url}`,
    })),
  };
}

// 生成网站结构化数据
export function generateWebsiteStructuredData(
  baseUrl: string = 'https://formalmath.example.com'
): object {
  return {
    '@context': 'https://schema.org',
    '@type': 'WebSite',
    name: 'FormalMath Interactive',
    url: baseUrl,
    description: '交互式数学可视化平台',
    potentialAction: {
      '@type': 'SearchAction',
      target: {
        '@type': 'EntryPoint',
        urlTemplate: `${baseUrl}/search?q={search_term_string}`,
      },
      'query-input': 'required name=search_term_string',
    },
  };
}

// 生成组织结构化数据
export function generateOrganizationStructuredData(
  baseUrl: string = 'https://formalmath.example.com'
): object {
  return {
    '@context': 'https://schema.org',
    '@type': 'Organization',
    name: 'FormalMath',
    url: baseUrl,
    logo: `${baseUrl}/FormalMath/icons/icon-192x192.png`,
    description: 'FormalMath是一个现代化的数学知识图谱可视化平台',
    sameAs: [
      'https://github.com/formalmath',
      'https://twitter.com/formalmath',
    ],
  };
}

// 生成教育应用结构化数据
export function generateEducationalAppStructuredData(
  baseUrl: string = 'https://formalmath.example.com'
): object {
  return {
    '@context': 'https://schema.org',
    '@type': 'LearningResource',
    name: 'FormalMath Interactive',
    description: '交互式数学学习与可视化平台',
    educationalLevel: '高等教育',
    learningResourceType: '交互式应用',
    interactivityType: 'active',
    url: baseUrl,
    author: {
      '@type': 'Organization',
      name: 'FormalMath Team',
    },
    educationalUse: ['自主学习', '课堂教学', '研究辅助'],
    teaches: ['数学概念', '数学证明', '逻辑推理'],
  };
}

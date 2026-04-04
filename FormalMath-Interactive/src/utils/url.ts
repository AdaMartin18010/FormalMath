/**
 * URL Utilities for FormalMath Interactive
 * URL优化工具函数
 */

/**
 * 生成SEO友好的URL slug
 */
export function generateSlug(text: string): string {
  if (!text) return '';
  
  return text
    .toString()
    .normalize('NFD') // 分解Unicode字符
    .replace(/[\u0300-\u036f]/g, '') // 移除音调符号
    .toLowerCase()
    .trim()
    .replace(/[^\w\s-]/g, '') // 移除非字母数字字符
    .replace(/[\s_-]+/g, '-') // 空格和下划线替换为连字符
    .replace(/^-+|-+$/g, ''); // 移除首尾连字符
}

/**
 * 生成概念详情页URL
 */
export function generateConceptUrl(conceptName: string, conceptId?: string): string {
  const slug = generateSlug(conceptName);
  if (conceptId) {
    return `/concept/${slug}-${conceptId}`;
  }
  return `/concept/${slug}`;
}

/**
 * 生成证明详情页URL
 */
export function generateProofUrl(theoremName: string, proofId?: string): string {
  const slug = generateSlug(theoremName);
  if (proofId) {
    return `/proof/${slug}-${proofId}`;
  }
  return `/proof/${slug}`;
}

/**
 * 生成分类页面URL
 */
export function generateCategoryUrl(categoryName: string): string {
  const slug = generateSlug(categoryName);
  return `/category/${slug}`;
}

/**
 * 生成搜索URL
 */
export function generateSearchUrl(query: string, filters?: Record<string, string>): string {
  const params = new URLSearchParams();
  params.set('q', query);
  
  if (filters) {
    Object.entries(filters).forEach(([key, value]) => {
      if (value) params.set(key, value);
    });
  }
  
  return `/search?${params.toString()}`;
}

/**
 * 解析概念URL获取ID
 */
export function parseConceptUrl(url: string): { name: string; id?: string } | null {
  const match = url.match(/\/concept\/(.+?)(?:-([a-f0-9]+))?$/);
  if (!match) return null;
  
  return {
    name: match[1].replace(/-/g, ' '),
    id: match[2],
  };
}

/**
 * 添加或更新URL参数
 */
export function updateUrlParam(
  url: string,
  key: string,
  value: string | null
): string {
  const [baseUrl, queryString] = url.split('?');
  const params = new URLSearchParams(queryString || '');
  
  if (value === null) {
    params.delete(key);
  } else {
    params.set(key, value);
  }
  
  const newQuery = params.toString();
  return newQuery ? `${baseUrl}?${newQuery}` : baseUrl;
}

/**
 * 移除URL参数
 */
export function removeUrlParam(url: string, key: string): string {
  return updateUrlParam(url, key, null);
}

/**
 * 获取URL参数
 */
export function getUrlParam(url: string, key: string): string | null {
  const [, queryString] = url.split('?');
  if (!queryString) return null;
  
  const params = new URLSearchParams(queryString);
  return params.get(key);
}

/**
 * 规范化URL（移除尾随斜杠、小写等）
 */
export function normalizeUrl(url: string): string {
  return url
    .toLowerCase()
    .replace(/\/+$/, '') // 移除尾随斜杠
    .replace(/\/+/g, '/'); // 合并多个斜杠
}

/**
 * 检查URL是否为外部链接
 */
export function isExternalUrl(url: string): boolean {
  return /^https?:\/\//.test(url) || /^\/\//.test(url);
}

/**
 * 生成面包屑URL
 */
export function generateBreadcrumbUrls(
  paths: { name: string; path?: string }[],
  basePath: string = ''
): { name: string; url: string }[] {
  let currentPath = basePath;
  
  return paths.map((item, index) => {
    if (item.path) {
      currentPath = item.path.startsWith('/') 
        ? item.path 
        : `${currentPath}/${item.path}`;
    }
    
    return {
      name: item.name,
      url: currentPath || '/',
    };
  });
}

/**
 * URL重定向映射表
 */
export const urlRedirects: Record<string, string> = {
  '/graph': '/knowledge-graph',
  '/tree': '/reasoning-tree',
  '/map': '/mind-map',
  '/compare': '/comparison',
  '/decision': '/decision-tree',
  '/history': '/evolution',
  '/dashboard': '/analytics',
  '/proof': '/proof-assistant',
  '/gallery': '/visualization-gallery',
};

/**
 * 检查并获取重定向URL
 */
export function getRedirectUrl(url: string): string | null {
  const normalized = normalizeUrl(url);
  return urlRedirects[normalized] || null;
}

/**
 * 生成多语言URL
 */
export function generateLocalizedUrl(
  path: string,
  locale: string,
  defaultLocale: string = 'zh-CN'
): string {
  if (locale === defaultLocale) {
    return path;
  }
  return `/${locale}${path}`;
}

/**
 * 从URL解析语言
 */
export function parseLocaleFromUrl(
  url: string,
  supportedLocales: string[] = ['zh-CN', 'en', 'ja']
): string {
  const pathMatch = url.match(/^\/([a-z]{2}(?:-[A-Z]{2})?)\//);
  if (pathMatch && supportedLocales.includes(pathMatch[1])) {
    return pathMatch[1];
  }
  return 'zh-CN';
}

/**
 * 生成分享URL
 */
export function generateShareUrl(
  path: string,
  params?: Record<string, string>
): string {
  const baseUrl = window.location.origin + path;
  if (!params || Object.keys(params).length === 0) {
    return baseUrl;
  }
  
  const searchParams = new URLSearchParams(params);
  return `${baseUrl}?${searchParams.toString()}`;
}

/**
 * 生成规范URL
 */
export function generateCanonicalUrl(
  path: string,
  baseUrl: string = 'https://formalmath.example.com'
): string {
  const normalizedPath = normalizeUrl(path);
  return `${baseUrl}${normalizedPath}`;
}

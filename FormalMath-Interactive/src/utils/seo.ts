// @ts-nocheck
/**
 * SEO Utilities for FormalMath Interactive
 * SEO工具函数
 */

import type { SEOMeta } from '@config/seo.config';

/**
 * 更新页面标题
 */
export function updatePageTitle(title: string): void {
  if (typeof document !== 'undefined') {
    document.title = title;
  }
}

/**
 * 更新meta标签
 */
export function updateMetaTag(name: string, content: string): void {
  if (typeof document === 'undefined') return;

  let meta = document.querySelector(`meta[name="${name}"]`) as HTMLMetaElement;
  if (!meta) {
    meta = document.createElement('meta');
    meta.name = name;
    document.head.appendChild(meta);
  }
  meta.content = content;
}

/**
 * 更新Open Graph标签
 */
export function updateOgTag(property: string, content: string): void {
  if (typeof document === 'undefined') return;

  let meta = document.querySelector(`meta[property="${property}"]`) as HTMLMetaElement;
  if (!meta) {
    meta = document.createElement('meta');
    meta.setAttribute('property', property);
    document.head.appendChild(meta);
  }
  meta.content = content;
}

/**
 * 更新Twitter Card标签
 */
export function updateTwitterTag(name: string, content: string): void {
  if (typeof document === 'undefined') return;

  let meta = document.querySelector(`meta[name="twitter:${name}"]`) as HTMLMetaElement;
  if (!meta) {
    meta = document.createElement('meta');
    meta.name = `twitter:${name}`;
    document.head.appendChild(meta);
  }
  meta.content = content;
}

/**
 * 更新canonical链接
 */
export function updateCanonicalUrl(url: string): void {
  if (typeof document === 'undefined') return;

  let link = document.querySelector('link[rel="canonical"]') as HTMLLinkElement;
  if (!link) {
    link = document.createElement('link');
    link.rel = 'canonical';
    document.head.appendChild(link);
  }
  link.href = url;
}

/**
 * 更新alternate语言链接
 */
export function updateAlternateLanguages(
  languages: Record<string, string>,
  currentPath: string = ''
): void {
  if (typeof document === 'undefined') return;

  // 移除现有的alternate链接
  document.querySelectorAll('link[rel="alternate"][hreflang]').forEach((el) => el.remove());

  // 添加新的alternate链接
  Object.entries(languages).forEach(([lang, baseUrl]) => {
    const link = document.createElement('link');
    link.rel = 'alternate';
    link.hreflang = lang;
    link.href = lang === 'zh-CN' 
      ? `${baseUrl}${currentPath}`
      : `${baseUrl}/${lang}${currentPath}`;
    document.head.appendChild(link);
  });

  // 添加x-default
  const defaultLink = document.createElement('link');
  defaultLink.rel = 'alternate';
  defaultLink.hreflang = 'x-default';
  defaultLink.href = languages['zh-CN'] || Object.values(languages)[0];
  document.head.appendChild(defaultLink);
}

/**
 * 添加/更新结构化数据脚本
 */
export function updateStructuredData(data: object | object[]): void {
  if (typeof document === 'undefined') return;

  // 移除现有的结构化数据
  document.querySelectorAll('script[type="application/ld+json"]').forEach((el) => el.remove());

  // 添加新的结构化数据
  const dataArray = Array.isArray(data) ? data : [data];
  dataArray.forEach((item) => {
    const script = document.createElement('script');
    script.type = 'application/ld+json';
    script.textContent = JSON.stringify(item, null, 2);
    document.head.appendChild(script);
  });
}

/**
 * 设置robots meta标签
 */
export function setRobotsMeta(noIndex: boolean, noFollow: boolean): void {
  if (typeof document === 'undefined') return;

  const content = [
    noIndex ? 'noindex' : 'index',
    noFollow ? 'nofollow' : 'follow',
  ].join(', ');

  updateMetaTag('robots', content);
}

/**
 * 应用完整的SEO配置
 */
export function applySEOConfig(
  config: SEOMeta,
  currentPath: string = '',
  baseUrl: string = 'https://formalmath.example.com'
): void {
  if (typeof document === 'undefined') return;

  // 更新标题
  updatePageTitle(config.title);

  // 更新基本meta标签
  if (config.description) {
    updateMetaTag('description', config.description);
  }
  if (config.keywords?.length) {
    updateMetaTag('keywords', config.keywords.join(', '));
  }

  // 更新Open Graph标签
  if (config.ogTitle) {
    updateOgTag('og:title', config.ogTitle);
  }
  if (config.ogDescription) {
    updateOgTag('og:description', config.ogDescription);
  }
  if (config.ogImage) {
    updateOgTag('og:image', baseUrl + config.ogImage);
  }
  if (config.ogType) {
    updateOgTag('og:type', config.ogType);
  }
  updateOgTag('og:url', `${baseUrl}${currentPath}`);

  // 更新Twitter Card标签
  if (config.twitterCard) {
    updateTwitterTag('card', config.twitterCard);
  }
  if (config.twitterTitle) {
    updateTwitterTag('title', config.twitterTitle);
  }
  if (config.twitterDescription) {
    updateTwitterTag('description', config.twitterDescription);
  }
  if (config.twitterImage) {
    updateTwitterTag('image', baseUrl + config.twitterImage);
  }

  // 更新canonical URL
  if (config.canonicalUrl) {
    updateCanonicalUrl(`${config.canonicalUrl}${currentPath}`);
  }

  // 更新alternate语言
  if (config.alternateLanguages) {
    updateAlternateLanguages(config.alternateLanguages, currentPath);
  }

  // 更新robots
  if (config.noIndex !== undefined || config.noFollow !== undefined) {
    setRobotsMeta(config.noIndex || false, config.noFollow || false);
  }

  // 更新结构化数据
  if (config.structuredData) {
    updateStructuredData(config.structuredData);
  }
}

/**
 * 生成URL友好的slug
 */
export function generateSlug(text: string): string {
  return text
    .toLowerCase()
    .replace(/[^\w\s-]/g, '')
    .replace(/[\s_-]+/g, '-')
    .replace(/^-+|-+$/g, '');
}

/**
 * 截断文本到指定长度
 */
export function truncateText(text: string, maxLength: number): string {
  if (text.length <= maxLength) return text;
  return text.substring(0, maxLength).replace(/\s+\S*$/, '') + '...';
}

/**
 * 生成页面预览描述
 */
export function generatePreview(
  content: string,
  maxLength: number = 160
): string {
  // 移除HTML标签
  const plainText = content.replace(/<[^>]*>/g, '');
  // 移除多余空白
  const cleaned = plainText.replace(/\s+/g, ' ').trim();
  // 截断
  return truncateText(cleaned, maxLength);
}

/**
 * 预加载关键资源
 */
export function preloadResource(
  href: string,
  as: 'script' | 'style' | 'image' | 'font' | 'fetch' = 'script',
  type?: string
): void {
  if (typeof document === 'undefined') return;

  // 检查是否已存在
  if (document.querySelector(`link[rel="preload"][href="${href}"]`)) {
    return;
  }

  const link = document.createElement('link');
  link.rel = 'preload';
  link.href = href;
  link.as = as;
  if (type) {
    link.type = type;
  }
  if (as === 'font') {
    link.crossOrigin = 'anonymous';
  }
  document.head.appendChild(link);
}

/**
 * 预连接到域名
 */
export function preconnectDomain(domain: string, crossOrigin: boolean = false): void {
  if (typeof document === 'undefined') return;

  // 检查是否已存在
  if (document.querySelector(`link[rel="preconnect"][href="${domain}"]`)) {
    return;
  }

  const link = document.createElement('link');
  link.rel = 'preconnect';
  link.href = domain;
  if (crossOrigin) {
    link.crossOrigin = 'anonymous';
  }
  document.head.appendChild(link);

  // 同时添加dns-prefetch
  const dnsLink = document.createElement('link');
  dnsLink.rel = 'dns-prefetch';
  dnsLink.href = domain;
  document.head.appendChild(dnsLink);
}

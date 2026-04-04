/**
 * SEO Head Component
 * 动态管理页面SEO的React组件
 */

import { useEffect } from 'react';
import { useLocation } from 'react-router-dom';
import {
  getPageSEO,
  generateBreadcrumbStructuredData,
  generateWebsiteStructuredData,
  generateOrganizationStructuredData,
  generateEducationalAppStructuredData,
} from '@config/seo.config';
import { applySEOConfig } from '@utils/seo';
import type { SEOMeta } from '@config/seo.config';

interface SEOHeadProps {
  pageKey?: string;
  customMeta?: Partial<SEOMeta>;
  baseUrl?: string;
  locale?: string;
}

/**
 * SEO Head 组件
 * 自动根据路由更新页面SEO
 */
export function SEOHead({
  pageKey,
  customMeta,
  baseUrl = 'https://formalmath.example.com',
  locale = 'zh-CN',
}: SEOHeadProps) {
  const location = useLocation();
  const currentPath = location.pathname;

  useEffect(() => {
    // 确定页面key
    const path = currentPath.replace('/FormalMath', '').replace(/^\//, '') || 'home';
    const key = pageKey || path || 'home';

    // 获取SEO配置
    const pageConfig = getPageSEO(key, locale);

    // 合并自定义meta
    const config: SEOMeta = {
      ...pageConfig,
      ...customMeta,
      // 合并结构化数据
      structuredData: [
        generateWebsiteStructuredData(baseUrl),
        generateOrganizationStructuredData(baseUrl),
        generateEducationalAppStructuredData(baseUrl),
        generateBreadcrumbStructuredData(key, baseUrl),
        ...(Array.isArray(customMeta?.structuredData)
          ? customMeta.structuredData
          : customMeta?.structuredData
          ? [customMeta.structuredData]
          : []),
      ],
    };

    // 应用SEO配置
    applySEOConfig(config, currentPath, baseUrl);

    // 更新HTML lang属性
    document.documentElement.lang = locale;
  }, [currentPath, pageKey, customMeta, baseUrl, locale]);

  // 这是一个无渲染组件
  return null;
}

export default SEOHead;

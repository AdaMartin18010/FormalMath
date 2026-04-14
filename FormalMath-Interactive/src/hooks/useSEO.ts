// @ts-nocheck
/**
 * SEO Hook for FormalMath Interactive
 * SEO相关的React Hook
 */

import { useEffect, useCallback } from 'react';
import { useLocation } from 'react-router-dom';
import {
  getPageSEO,
  generateBreadcrumbStructuredData,
  generateWebsiteStructuredData,
  generateOrganizationStructuredData,
  generateEducationalAppStructuredData,
} from '@config/seo.config';
import { applySEOConfig, preconnectDomain, preloadResource } from '@utils/seo';
import type { SEOMeta } from '@config/seo.config';

interface UseSEOOptions {
  pageKey?: string;
  customMeta?: Partial<SEOMeta>;
  baseUrl?: string;
  locale?: string;
  preloadAssets?: string[];
  preconnectDomains?: string[];
}

/**
 * SEO Hook
 * 用于在组件中动态管理页面SEO
 */
export function useSEO(options: UseSEOOptions = {}) {
  const {
    pageKey,
    customMeta,
    baseUrl = 'https://formalmath.example.com',
    locale = 'zh-CN',
    preloadAssets = [],
    preconnectDomains = [],
  } = options;

  const location = useLocation();

  // 预连接域名
  useEffect(() => {
    preconnectDomains.forEach((domain) => {
      preconnectDomain(domain, true);
    });
  }, [preconnectDomains]);

  // 预加载资源
  useEffect(() => {
    preloadAssets.forEach((asset) => {
      const ext = asset.split('.').pop();
      const as = ext === 'css' ? 'style' : ext === 'js' ? 'script' : 'fetch';
      preloadResource(asset, as as any);
    });
  }, [preloadAssets]);

  // 应用SEO配置
  useEffect(() => {
    const path = location.pathname.replace('/FormalMath', '').replace(/^\//, '') || 'home';
    const key = pageKey || path || 'home';

    const pageConfig = getPageSEO(key, locale);

    const config: SEOMeta = {
      ...pageConfig,
      ...customMeta,
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

    applySEOConfig(config, location.pathname, baseUrl);
    document.documentElement.lang = locale;
  }, [location.pathname, pageKey, customMeta, baseUrl, locale]);

  // 手动更新SEO的方法
  const updateSEO = useCallback(
    (meta: Partial<SEOMeta>) => {
      const path = location.pathname.replace('/FormalMath', '').replace(/^\//, '') || 'home';
      const key = pageKey || path || 'home';
      const pageConfig = getPageSEO(key, locale);

      const config: SEOMeta = {
        ...pageConfig,
        ...meta,
      };

      applySEOConfig(config, location.pathname, baseUrl);
    },
    [location.pathname, pageKey, baseUrl, locale]
  );

  // 设置无索引标记
  const setNoIndex = useCallback(
    (noIndex: boolean = true) => {
      updateSEO({ noIndex });
    },
    [updateSEO]
  );

  return {
    updateSEO,
    setNoIndex,
    currentPath: location.pathname,
  };
}

/**
 * 页面特定的SEO Hook
 */
export function usePageSEO(pageKey: string, customMeta?: Partial<SEOMeta>) {
  return useSEO({
    pageKey,
    customMeta,
  });
}

/**
 * 概念详情页SEO Hook
 */
export function useConceptSEO(
  conceptName: string,
  conceptDescription?: string,
  conceptKeywords?: string[]
) {
  return useSEO({
    pageKey: 'concept-detail',
    customMeta: {
      title: `${conceptName} - 数学概念 | FormalMath`,
      description: conceptDescription || `${conceptName}的详细解释、定义、性质和相关概念`,
      keywords: [
        conceptName,
        '数学概念',
        '数学定义',
        ...(conceptKeywords || []),
      ],
      ogType: 'article',
    },
  });
}

/**
 * 预加载关键资源的Hook
 */
export function usePreloadAssets(assets: string[]) {
  useEffect(() => {
    assets.forEach((asset) => {
      const ext = asset.split('.').pop();
      const as = ext === 'css' ? 'style' : ext === 'js' ? 'script' : 'fetch';
      preloadResource(asset, as as any);
    });
  }, [assets]);
}

export default useSEO;

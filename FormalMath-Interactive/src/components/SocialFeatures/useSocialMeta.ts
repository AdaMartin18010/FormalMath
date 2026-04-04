import { useState, useEffect, useCallback, useRef } from 'react';
import type { OpenGraphMetaProps } from './OpenGraphMeta';

export interface UseSocialMetaOptions {
  title: string;
  description: string;
  url?: string;
  image?: string;
  type?: 'website' | 'article' | 'profile';
  keywords?: string[];
  author?: string;
  publishedTime?: string;
  modifiedTime?: string;
  section?: string;
  tags?: string[];
  twitterCard?: 'summary' | 'summary_large_image' | 'app' | 'player';
  twitterSite?: string;
  twitterCreator?: string;
  updateDocument?: boolean;
}

export interface UseShareCountResult {
  counts: Record<string, number>;
  loading: boolean;
  error: string | null;
  refresh: () => void;
}

// 动态更新文档 meta 标签
const updateMetaTags = (meta: Partial<OpenGraphMetaProps>) => {
  if (typeof document === 'undefined') return;

  const setMeta = (property: string, content?: string, isName = false) => {
    if (!content) return;
    
    const selector = isName 
      ? `meta[name="${property}"]` 
      : `meta[property="${property}"]`;
    
    let element = document.querySelector(selector) as HTMLMetaElement;
    
    if (!element) {
      element = document.createElement('meta');
      if (isName) {
        element.name = property;
      } else {
        element.setAttribute('property', property);
      }
      document.head.appendChild(element);
    }
    
    element.content = content;
  };

  // Basic
  if (meta.title) {
    document.title = meta.title;
    setMeta('og:title', meta.title);
    setMeta('twitter:title', meta.title);
  }
  
  if (meta.description) {
    setMeta('description', meta.description, true);
    setMeta('og:description', meta.description);
    setMeta('twitter:description', meta.description);
  }

  // Open Graph
  if (meta.url) setMeta('og:url', meta.url);
  if (meta.type) setMeta('og:type', meta.type);
  if (meta.siteName) setMeta('og:site_name', meta.siteName);
  if (meta.locale) setMeta('og:locale', meta.locale);
  
  if (meta.image) {
    setMeta('og:image', meta.image);
    setMeta('twitter:image', meta.image);
    setMeta('og:image:width', '1200');
    setMeta('og:image:height', '630');
  }

  // Twitter
  if (meta.twitterCard) setMeta('twitter:card', meta.twitterCard, true);
  if (meta.twitterSite) setMeta('twitter:site', meta.twitterSite, true);
  if (meta.twitterCreator) setMeta('twitter:creator', meta.twitterCreator, true);

  // Article
  if (meta.publishedTime) setMeta('article:published_time', meta.publishedTime);
  if (meta.modifiedTime) setMeta('article:modified_time', meta.modifiedTime);
  if (meta.section) setMeta('article:section', meta.section);
  if (meta.tags) {
    meta.tags.forEach(tag => setMeta('article:tag', tag));
  }

  // Keywords
  if (meta.keywords) {
    setMeta('keywords', meta.keywords.join(', '), true);
  }
};

// 获取分享计数
const fetchShareCount = async (url: string, platform: string): Promise<number> => {
  const endpoints: Record<string, string> = {
    facebook: `https://graph.facebook.com/?id=${encodeURIComponent(url)}&fields=engagement`,
    pinterest: `https://api.pinterest.com/v1/urls/count.json?url=${encodeURIComponent(url)}`,
    reddit: `https://www.reddit.com/api/info.json?url=${encodeURIComponent(url)}`,
  };

  const endpoint = endpoints[platform];
  if (!endpoint) return 0;

  try {
    const response = await fetch(endpoint);
    const data = await response.json();

    switch (platform) {
      case 'facebook':
        return data.engagement?.share_count || 0;
      case 'pinterest':
        return data.count || 0;
      case 'reddit':
        return data.data?.children?.reduce((sum: number, child: any) => 
          sum + child.data.score, 0
        ) || 0;
      default:
        return 0;
    }
  } catch (error) {
    console.warn(`Failed to fetch ${platform} share count:`, error);
    return 0;
  }
};

// 社交元数据 Hook
export const useSocialMeta = (options: UseSocialMetaOptions) => {
  const { updateDocument = true, ...metaOptions } = options;
  const isFirstRender = useRef(true);

  useEffect(() => {
    if (!updateDocument || typeof document === 'undefined') return;

    // 更新 meta 标签
    updateMetaTags({
      ...metaOptions,
      siteName: metaOptions.twitterSite || 'FormalMath',
      locale: 'zh_CN',
      twitterCard: metaOptions.twitterCard || 'summary_large_image',
    });

    // 清理函数（恢复原始标题）
    if (isFirstRender.current) {
      isFirstRender.current = false;
      const originalTitle = document.title;
      return () => {
        document.title = originalTitle;
      };
    }
  }, [
    updateDocument,
    metaOptions.title,
    metaOptions.description,
    metaOptions.url,
    metaOptions.image,
    metaOptions.type,
    metaOptions.keywords?.join(','),
    metaOptions.tags?.join(','),
  ]);

  // 生成分享链接
  const generateShareUrl = useCallback((platform: string): string => {
    const { title = '', description = '', url = window.location.href, image = '' } = metaOptions;
    
    const shareUrls: Record<string, string> = {
      twitter: `https://twitter.com/intent/tweet?url=${encodeURIComponent(url)}&text=${encodeURIComponent(title)}`,
      facebook: `https://www.facebook.com/sharer/sharer.php?u=${encodeURIComponent(url)}`,
      linkedin: `https://www.linkedin.com/sharing/share-offsite/?url=${encodeURIComponent(url)}`,
      weibo: `https://service.weibo.com/share/share.php?url=${encodeURIComponent(url)}&title=${encodeURIComponent(title)}&pic=${encodeURIComponent(image)}`,
      email: `mailto:?subject=${encodeURIComponent(title)}&body=${encodeURIComponent(description + '\n\n' + url)}`,
    };

    return shareUrls[platform] || url;
  }, [metaOptions]);

  // 分享功能
  const share = useCallback((platform: string, customUrl?: string): void => {
    const url = customUrl || generateShareUrl(platform);
    
    if (platform === 'native' && navigator.share) {
      navigator.share({
        title: metaOptions.title,
        text: metaOptions.description,
        url: customUrl || metaOptions.url || window.location.href,
      }).catch(() => {
        // User cancelled
      });
    } else {
      window.open(url, `${platform}Share`, 'width=600,height=400,scrollbars=yes');
    }
  }, [generateShareUrl, metaOptions]);

  return {
    share,
    generateShareUrl,
    meta: metaOptions,
  };
};

// 分享计数 Hook
export const useShareCount = (url: string, platforms: string[] = ['facebook']): UseShareCountResult => {
  const [counts, setCounts] = useState<Record<string, number>>({});
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const fetchCounts = useCallback(async () => {
    setLoading(true);
    setError(null);

    try {
      const results = await Promise.all(
        platforms.map(async (platform) => ({
          platform,
          count: await fetchShareCount(url, platform),
        }))
      );

      const newCounts = results.reduce((acc, { platform, count }) => {
        acc[platform] = count;
        return acc;
      }, {} as Record<string, number>);

      setCounts(newCounts);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Failed to fetch share counts');
    } finally {
      setLoading(false);
    }
  }, [url, platforms.join(',')]);

  useEffect(() => {
    fetchCounts();
  }, [fetchCounts]);

  return {
    counts,
    loading,
    error,
    refresh: fetchCounts,
  };
};

// 预取分享计数（用于服务端渲染或静态生成）
export const prefetchShareCounts = async (
  urls: string[],
  platforms: string[] = ['facebook']
): Promise<Record<string, Record<string, number>>> => {
  const results: Record<string, Record<string, number>> = {};

  await Promise.all(
    urls.map(async (url) => {
      results[url] = {};
      await Promise.all(
        platforms.map(async (platform) => {
          results[url][platform] = await fetchShareCount(url, platform);
        })
      );
    })
  );

  return results;
};

export default useSocialMeta;

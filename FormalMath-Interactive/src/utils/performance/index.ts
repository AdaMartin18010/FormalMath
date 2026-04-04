/**
 * 性能优化工具导出
 */

export { lazyLoad, preloadComponent, createLazyComponent, createLazyImageLoader, loadPolyfill, chunkedLoad, calculateVirtualRange } from './lazyLoad';
export type { LazyLoadOptions, VirtualListConfig, VirtualListRange } from './lazyLoad';

export { LRUCache, withCache, storageCache } from './cache';

// 默认导出
export { default } from './lazyLoad';

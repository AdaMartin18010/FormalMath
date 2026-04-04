/**
 * 国际化模块导出
 */

export { default as i18n, i18nConfig } from './config';
export {
  isRTLLanguage,
  getLanguageDirection,
  getLanguageInfo,
  SUPPORTED_LANGUAGES,
  RTL_LANGUAGES,
  translateWithNamespace,
  loadLanguageResources,
} from './config';
export type { SupportedLanguage } from './config';

// 默认导出
export { default } from './config';

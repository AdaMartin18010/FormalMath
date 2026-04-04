/**
 * 国际化配置 - i18n Configuration
 * 支持RTL语言（阿拉伯语、希伯来语）和多语言切换
 */

import i18n from 'i18next';
import { initReactI18next } from 'react-i18next';
import LanguageDetector from 'i18next-browser-languagedetector';

// 导入语言资源
import en from './locales/en.json';
import zh from './locales/zh.json';
import ar from './locales/ar.json';
import he from './locales/he.json';

// RTL语言列表
export const RTL_LANGUAGES = ['ar', 'he'] as const;

// 支持的语言
export const SUPPORTED_LANGUAGES = [
  { code: 'en', name: 'English', nativeName: 'English', dir: 'ltr' },
  { code: 'zh', name: 'Chinese', nativeName: '中文', dir: 'ltr' },
  { code: 'ar', name: 'Arabic', nativeName: 'العربية', dir: 'rtl' },
  { code: 'he', name: 'Hebrew', nativeName: 'עברית', dir: 'rtl' },
] as const;

export type SupportedLanguage = typeof SUPPORTED_LANGUAGES[number]['code'];

// 检测是否为RTL语言
export const isRTLLanguage = (lang: string): boolean => {
  return RTL_LANGUAGES.includes(lang as typeof RTL_LANGUAGES[number]);
};

// 获取语言方向
export const getLanguageDirection = (lang: string): 'ltr' | 'rtl' => {
  return isRTLLanguage(lang) ? 'rtl' : 'ltr';
};

// 获取语言信息
export const getLanguageInfo = (code: string) => {
  return SUPPORTED_LANGUAGES.find(lang => lang.code === code) || SUPPORTED_LANGUAGES[0];
};

// 语言资源
const resources = {
  en: { translation: en },
  zh: { translation: zh },
  ar: { translation: ar },
  he: { translation: he },
};

// i18n配置选项
export const i18nConfig = {
  resources,
  fallbackLng: 'en',
  debug: process.env.NODE_ENV === 'development',
  
  detection: {
    order: ['localStorage', 'navigator', 'htmlTag'],
    caches: ['localStorage'],
    lookupLocalStorage: 'i18nextLng',
  },
  
  interpolation: {
    escapeValue: false,
  },
  
  react: {
    useSuspense: false,
    bindI18n: 'languageChanged loaded',
    bindStore: 'added removed',
    nsMode: 'default',
  },
  
  pluralSeparator: '_',
  nsSeparator: ':',
  partialBundledLanguages: true,
  
  saveMissing: process.env.NODE_ENV === 'development',
  missingKeyHandler: (lng: string, ns: string, key: string) => {
    console.warn(`Missing translation key: ${key} in ${lng}.${ns}`);
  },
};

// 初始化i18n
if (!i18n.isInitialized) {
  i18n
    .use(LanguageDetector)
    .use(initReactI18next)
    .init(i18nConfig);
}

// 语言切换事件监听
i18n.on('languageChanged', (lng: string) => {
  document.documentElement.dir = getLanguageDirection(lng);
  document.documentElement.lang = lng;
  window.dispatchEvent(new CustomEvent('languagechange', { detail: { language: lng } }));
});

export default i18n;

// 辅助函数：带命名空间的翻译
export const translateWithNamespace = (namespace: string) => {
  return (key: string, options?: Record<string, unknown>) => {
    return i18n.t(`${namespace}:${key}`, options);
  };
};

// 动态加载语言资源
export const loadLanguageResources = async (lang: SupportedLanguage) => {
  try {
    const resources = await import(`./locales/${lang}.json`);
    i18n.addResourceBundle(lang, 'translation', resources.default, true, true);
    return true;
  } catch (error) {
    console.error(`Failed to load language resources for ${lang}:`, error);
    return false;
  }
};

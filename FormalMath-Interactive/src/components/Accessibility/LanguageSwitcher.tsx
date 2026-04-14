// @ts-nocheck
/**
 * 语言切换器组件
 * 支持多语言和RTL切换
 */

import React, { useState, useRef, useCallback } from 'react';
import { useTranslation } from 'react-i18next';
import { Globe, Check } from 'lucide-react';
import { cn } from '@utils/classNames';
import { SUPPORTED_LANGUAGES, getLanguageInfo, type SupportedLanguage } from '@i18n/config';
import { useFocusTrap } from '@hooks/a11y/useFocus';
import { useAnnounce } from '@hooks/a11y/useAnnounce';

interface LanguageSwitcherProps {
  variant?: 'dropdown' | 'inline' | 'minimal';
  showFlags?: boolean;
  className?: string;
}

/**
 * 语言切换器
 */
export const LanguageSwitcher: React.FC<LanguageSwitcherProps> = ({
  variant = 'dropdown',
  showFlags = false,
  className,
}) => {
  const { i18n, t } = useTranslation();
  const [isOpen, setIsOpen] = useState(false);
  const { announce } = useAnnounce();
  const currentLanguage = i18n.language;

  const containerRef = useFocusTrap<HTMLDivElement>({
    enabled: isOpen,
    onEscape: () => setIsOpen(false),
    returnFocus: true,
  });

  const handleLanguageChange = useCallback((langCode: SupportedLanguage) => {
    const langInfo = getLanguageInfo(langCode);
    
    i18n.changeLanguage(langCode).then(() => {
      announce(`语言已切换为 ${langInfo.nativeName}`, { 
        priority: 'polite',
        level: 'success' 
      });
      setIsOpen(false);
    });
  }, [i18n, announce]);

  const currentLangInfo = getLanguageInfo(currentLanguage);

  // 获取国旗emoji
  const getFlagEmoji = (code: string) => {
    const flags: Record<string, string> = {
      en: '🇺🇸',
      zh: '🇨🇳',
      ar: '🇸🇦',
      he: '🇮🇱',
      ja: '🇯🇵',
      ko: '🇰🇷',
      es: '🇪🇸',
      fr: '🇫🇷',
      de: '🇩🇪',
      ru: '🇷🇺',
    };
    return flags[code] || '🌐';
  };

  if (variant === 'minimal') {
    return (
      <button
        onClick={() => handleLanguageChange(
          SUPPORTED_LANGUAGES[
            (SUPPORTED_LANGUAGES.findIndex(l => l.code === currentLanguage) + 1) % SUPPORTED_LANGUAGES.length
          ].code
        )}
        className={cn(
          'p-2 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-800',
          'focus:outline-none focus-visible:ring-2 focus-visible:ring-blue-500',
          'transition-colors',
          className
        )}
        aria-label={t('accessibility.toggleLanguage')}
        title={t('accessibility.toggleLanguage')}
      >
        <span className="text-lg">{getFlagEmoji(currentLanguage)}</span>
      </button>
    );
  }

  if (variant === 'inline') {
    return (
      <div className={cn('flex items-center gap-1', className)} role="group" aria-label="语言选择">
        {SUPPORTED_LANGUAGES.map((lang) => (
          <button
            key={lang.code}
            onClick={() => handleLanguageChange(lang.code)}
            className={cn(
              'px-3 py-1.5 text-sm font-medium rounded-md transition-colors',
              'focus:outline-none focus-visible:ring-2 focus-visible:ring-blue-500',
              currentLanguage === lang.code
                ? 'bg-blue-100 text-blue-700 dark:bg-blue-900/30 dark:text-blue-400'
                : 'text-gray-600 hover:bg-gray-100 dark:text-gray-400 dark:hover:bg-slate-800'
            )}
            aria-pressed={currentLanguage === lang.code}
          >
            {showFlags && <span className="mr-1.5">{getFlagEmoji(lang.code)}</span>}
            {lang.code.toUpperCase()}
          </button>
        ))}
      </div>
    );
  }

  // Dropdown variant
  return (
    <div ref={containerRef} className={cn('relative', className)}>
      <button
        onClick={() => setIsOpen(!isOpen)}
        className={cn(
          'flex items-center gap-2 px-3 py-2 text-sm font-medium',
          'text-gray-700 dark:text-gray-300',
          'hover:bg-gray-100 dark:hover:bg-slate-800',
          'rounded-lg transition-colors',
          'focus:outline-none focus-visible:ring-2 focus-visible:ring-blue-500',
          isOpen && 'bg-gray-100 dark:bg-slate-800'
        )}
        aria-expanded={isOpen}
        aria-haspopup="listbox"
        aria-label={t('accessibility.toggleLanguage')}
      >
        <Globe className="w-4 h-4" aria-hidden="true" />
        <span>{currentLangInfo.nativeName}</span>
      </button>

      {isOpen && (
        <div
          className={cn(
            'absolute z-50 mt-2 min-w-[180px]',
            'bg-white dark:bg-slate-800',
            'rounded-lg shadow-lg border border-gray-200 dark:border-slate-700',
            'py-1'
          )}
          role="listbox"
          aria-label="可用语言"
        >
          {SUPPORTED_LANGUAGES.map((lang) => (
            <button
              key={lang.code}
              onClick={() => handleLanguageChange(lang.code)}
              role="option"
              aria-selected={currentLanguage === lang.code}
              className={cn(
                'w-full flex items-center justify-between px-4 py-2 text-sm',
                'hover:bg-gray-100 dark:hover:bg-slate-700',
                'focus:outline-none focus-visible:bg-gray-100 dark:focus-visible:bg-slate-700',
                currentLanguage === lang.code
                  ? 'text-blue-600 dark:text-blue-400'
                  : 'text-gray-700 dark:text-gray-300'
              )}
            >
              <span className="flex items-center gap-2">
                {showFlags && <span>{getFlagEmoji(lang.code)}</span>}
                <span>{lang.nativeName}</span>
                <span className="text-gray-400 text-xs">({lang.name})</span>
              </span>
              {currentLanguage === lang.code && (
                <Check className="w-4 h-4" aria-hidden="true" />
              )}
            </button>
          ))}
        </div>
      )}

      {/* Backdrop for closing dropdown */}
      {isOpen && (
        <div
          className="fixed inset-0 z-40"
          onClick={() => setIsOpen(false)}
          aria-hidden="true"
        />
      )}
    </div>
  );
};

/**
 * 紧凑语言切换器（仅用于移动端）
 */
export const CompactLanguageSwitcher: React.FC<{ className?: string }> = ({ className }) => {
  const { i18n } = useTranslation();
  const [isOpen, setIsOpen] = useState(false);
  const containerRef = useFocusTrap<HTMLDivElement>({
    enabled: isOpen,
    onEscape: () => setIsOpen(false),
  });

  const handleSelect = (code: SupportedLanguage) => {
    i18n.changeLanguage(code);
    setIsOpen(false);
  };

  return (
    <div ref={containerRef} className={cn('relative', className)}>
      <button
        onClick={() => setIsOpen(!isOpen)}
        className="p-2 rounded-full bg-gray-100 dark:bg-slate-800 text-gray-700 dark:text-gray-300"
        aria-expanded={isOpen}
      >
        <Globe className="w-5 h-5" />
      </button>

      {isOpen && (
        <div className="absolute right-0 z-50 mt-2 w-48 bg-white dark:bg-slate-800 rounded-lg shadow-lg border border-gray-200 dark:border-slate-700 py-1">
          {SUPPORTED_LANGUAGES.map((lang) => (
            <button
              key={lang.code}
              onClick={() => handleSelect(lang.code)}
              className={cn(
                'w-full text-left px-4 py-2 text-sm',
                i18n.language === lang.code
                  ? 'bg-blue-50 text-blue-600 dark:bg-blue-900/30 dark:text-blue-400'
                  : 'text-gray-700 dark:text-gray-300'
              )}
            >
              {lang.nativeName}
            </button>
          ))}
        </div>
      )}

      {isOpen && (
        <div className="fixed inset-0 z-40" onClick={() => setIsOpen(false)} />
      )}
    </div>
  );
};

export default LanguageSwitcher;

// @ts-nocheck
/**
 * 文化适配组件
 * 处理不同文化背景下的UI差异
 */

import React, { createContext, useContext, useMemo } from 'react';
import { useTranslation } from 'react-i18next';
import { getLanguageInfo, isRTLLanguage } from '@i18n/config';

// 文化区域类型
type CulturalRegion = 'east-asia' | 'middle-east' | 'western' | 'default';

interface CulturalContextType {
  region: CulturalRegion;
  isRTL: boolean;
  isCompact: boolean;
  colorScheme: 'vibrant' | 'muted' | 'monochrome';
  dateFormat: 'iso' | 'localized';
  numberFormat: 'western' | 'arabic-indic' | 'eastern-arabic';
}

const CulturalContext = createContext<CulturalContextType>({
  region: 'default',
  isRTL: false,
  isCompact: false,
  colorScheme: 'vibrant',
  dateFormat: 'iso',
  numberFormat: 'western',
});

export const useCulturalContext = () => useContext(CulturalContext);

/**
 * 文化适配Provider
 */
export const CulturalProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const { i18n } = useTranslation();
  const language = i18n.language;

  const context = useMemo((): CulturalContextType => {
    const langInfo = getLanguageInfo(language);
    
    // 根据语言确定文化区域
    let region: CulturalRegion = 'default';
    if (['zh', 'ja', 'ko'].includes(language)) {
      region = 'east-asia';
    } else if (['ar', 'he', 'fa', 'ur'].includes(language)) {
      region = 'middle-east';
    } else if (['en', 'fr', 'de', 'es', 'it', 'pt'].includes(language)) {
      region = 'western';
    }

    // 紧凑模式（东亚语言通常更适合紧凑布局）
    const isCompact = region === 'east-asia';

    // 色彩方案偏好
    let colorScheme: 'vibrant' | 'muted' | 'monochrome' = 'vibrant';
    if (region === 'middle-east') {
      colorScheme = 'muted';
    }

    // 日期格式
    const dateFormat: 'iso' | 'localized' = region === 'western' ? 'iso' : 'localized';

    // 数字格式
    let numberFormat: 'western' | 'arabic-indic' | 'eastern-arabic' = 'western';
    if (language === 'ar') {
      numberFormat = 'arabic-indic';
    } else if (['fa', 'ur'].includes(language)) {
      numberFormat = 'eastern-arabic';
    }

    return {
      region,
      isRTL: isRTLLanguage(language),
      isCompact,
      colorScheme,
      dateFormat,
      numberFormat,
    };
  }, [language]);

  return (
    <CulturalContext.Provider value={context}>
      {children}
    </CulturalContext.Provider>
  );
};

/**
 * 文化敏感日期格式化
 */
export const CulturalDate: React.FC<{
  date: Date | string | number;
  format?: 'short' | 'long' | 'relative';
  className?: string;
}> = ({ date, format = 'short', className }) => {
  const { dateFormat } = useCulturalContext();
  const { i18n } = useTranslation();

  const formattedDate = useMemo(() => {
    const d = new Date(date);
    
    if (format === 'relative') {
      // 相对时间（使用Intl.RelativeTimeFormat）
      const now = new Date();
      const diffInDays = Math.floor((now.getTime() - d.getTime()) / (1000 * 60 * 60 * 24));
      
      const rtf = new Intl.RelativeTimeFormat(i18n.language, { numeric: 'auto' });
      
      if (diffInDays < 1) return rtf.format(0, 'day');
      if (diffInDays < 7) return rtf.format(-diffInDays, 'day');
      if (diffInDays < 30) return rtf.format(-Math.floor(diffInDays / 7), 'week');
      if (diffInDays < 365) return rtf.format(-Math.floor(diffInDays / 30), 'month');
      return rtf.format(-Math.floor(diffInDays / 365), 'year');
    }

    // 格式化日期
    const options: Intl.DateTimeFormatOptions = format === 'long'
      ? { year: 'numeric', month: 'long', day: 'numeric' }
      : { year: 'numeric', month: 'short', day: 'numeric' };

    return new Intl.DateTimeFormat(i18n.language, options).format(d);
  }, [date, format, i18n.language]);

  return <time dateTime={new Date(date).toISOString()} className={className}>
    {formattedDate}
  </time>;
};

/**
 * 文化敏感数字格式化
 */
export const CulturalNumber: React.FC<{
  value: number;
  format?: 'decimal' | 'percent' | 'currency';
  currency?: string;
  className?: string;
}> = ({ value, format = 'decimal', currency = 'USD', className }) => {
  const { numberFormat, region } = useCulturalContext();
  const { i18n } = useTranslation();

  const formattedNumber = useMemo(() => {
    const options: Intl.NumberFormatOptions = {};

    if (format === 'percent') {
      options.style = 'percent';
    } else if (format === 'currency') {
      options.style = 'currency';
      options.currency = currency;
    }

    // 使用适当的数字系统
    if (numberFormat === 'arabic-indic') {
      options.numberingSystem = 'arab';
    } else if (numberFormat === 'eastern-arabic') {
      options.numberingSystem = 'arabext';
    }

    return new Intl.NumberFormat(i18n.language, options).format(value);
  }, [value, format, currency, numberFormat, i18n.language]);

  return <span className={className} dir={region === 'middle-east' ? 'rtl' : 'ltr'}>
    {formattedNumber}
  </span>;
};

/**
 * 文化敏感间距组件
 * 根据文化区域调整间距
 */
export const CulturalSpacing: React.FC<{
  children: React.ReactNode;
  density?: 'compact' | 'comfortable' | 'spacious';
  className?: string;
}> = ({ children, density, className }) => {
  const { isCompact, region } = useCulturalContext();

  const spacingClass = useMemo(() => {
    const effectiveDensity = density || (isCompact ? 'compact' : 'comfortable');
    
    const spacingMap = {
      compact: 'space-y-2',
      comfortable: 'space-y-4',
      spacious: 'space-y-6',
    };

    return spacingMap[effectiveDensity];
  }, [density, isCompact]);

  return (
    <div className={`${spacingClass} ${region === 'middle-east' ? 'text-right' : ''} ${className || ''}`}>
      {children}
    </div>
  );
};

/**
 * 文化敏感图标
 * 某些文化中对特定图标有不同理解
 */
export const CulturalIcon: React.FC<{
  icon: React.ReactNode;
  altIcon?: React.ReactNode;
  sensitiveIn?: string[];
  className?: string;
}> = ({ icon, altIcon, sensitiveIn = ['middle-east'], className }) => {
  const { region } = useCulturalContext();

  const shouldUseAlt = sensitiveIn.includes(region);

  return (
    <span className={className}>
      {shouldUseAlt && altIcon ? altIcon : icon}
    </span>
  );
};

export default CulturalProvider;

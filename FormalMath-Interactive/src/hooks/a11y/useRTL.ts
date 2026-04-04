/**
 * RTL (Right-to-Left) 支持 Hook
 * 用于处理阿拉伯语、希伯来语等从右到左语言布局
 */

import { useEffect, useCallback, useState } from 'react';
import { useTranslation } from 'react-i18next';
import { isRTLLanguage, getLanguageDirection } from '@i18n/config';

interface UseRTLReturn {
  isRTL: boolean;
  direction: 'ltr' | 'rtl';
  toggleDirection: () => void;
  setDirection: (dir: 'ltr' | 'rtl') => void;
  mirrorClass: string;
  flipClass: string;
}

/**
 * 检测并使用RTL布局
 */
export const useRTL = (): UseRTLReturn => {
  const { i18n } = useTranslation();
  const [isRTL, setIsRTL] = useState(() => isRTLLanguage(i18n.language));
  const [direction, setDirectionState] = useState<'ltr' | 'rtl'>(() => 
    getLanguageDirection(i18n.language)
  );

  // 监听语言变化
  useEffect(() => {
    const handleLanguageChange = (lng: string) => {
      const newDirection = getLanguageDirection(lng);
      setIsRTL(isRTLLanguage(lng));
      setDirectionState(newDirection);
    };

    // 初始检测
    handleLanguageChange(i18n.language);

    // 订阅i18n事件
    i18n.on('languageChanged', handleLanguageChange);

    return () => {
      i18n.off('languageChanged', handleLanguageChange);
    };
  }, [i18n]);

  // 切换方向
  const toggleDirection = useCallback(() => {
    const newDirection = direction === 'ltr' ? 'rtl' : 'ltr';
    setDirection(newDirection);
  }, [direction]);

  // 设置方向
  const setDirection = useCallback((dir: 'ltr' | 'rtl') => {
    setDirectionState(dir);
    setIsRTL(dir === 'rtl');
    document.documentElement.dir = dir;
  }, []);

  // 镜像类名（用于RTL时翻转元素）
  const mirrorClass = isRTL ? 'rtl-mirror' : '';
  
  // 翻转类名（用于图标等）
  const flipClass = isRTL ? 'rtl-flip' : '';

  return {
    isRTL,
    direction,
    toggleDirection,
    setDirection,
    mirrorClass,
    flipClass,
  };
};

/**
 * RTL 样式 Hook - 返回基于方向的样式对象
 */
export const useRTLStyles = () => {
  const { isRTL } = useRTL();

  const getMarginStart = useCallback((value: string | number) => ({
    marginLeft: isRTL ? undefined : value,
    marginRight: isRTL ? value : undefined,
  }), [isRTL]);

  const getMarginEnd = useCallback((value: string | number) => ({
    marginLeft: isRTL ? value : undefined,
    marginRight: isRTL ? undefined : value,
  }), [isRTL]);

  const getPaddingStart = useCallback((value: string | number) => ({
    paddingLeft: isRTL ? undefined : value,
    paddingRight: isRTL ? value : undefined,
  }), [isRTL]);

  const getPaddingEnd = useCallback((value: string | number) => ({
    paddingLeft: isRTL ? value : undefined,
    paddingRight: isRTL ? undefined : value,
  }), [isRTL]);

  const getBorderStart = useCallback((width: string, style: string, color: string) => ({
    borderLeft: isRTL ? undefined : `${width} ${style} ${color}`,
    borderRight: isRTL ? `${width} ${style} ${color}` : undefined,
  }), [isRTL]);

  const getBorderEnd = useCallback((width: string, style: string, color: string) => ({
    borderLeft: isRTL ? `${width} ${style} ${color}` : undefined,
    borderRight: isRTL ? undefined : `${width} ${style} ${color}`,
  }), [isRTL]);

  const getTextAlign = useCallback((align: 'left' | 'right' | 'center' | 'justify') => {
    if (align === 'left') return { textAlign: isRTL ? 'right' : 'left' };
    if (align === 'right') return { textAlign: isRTL ? 'left' : 'right' };
    return { textAlign: align };
  }, [isRTL]);

  const getTransformOrigin = useCallback((origin: string) => {
    if (!isRTL) return { transformOrigin: origin };
    
    // 翻转transform-origin
    const flipped = origin
      .replace('left', '%%L%%')
      .replace('right', 'left')
      .replace('%%L%%', 'right');
    
    return { transformOrigin: flipped };
  }, [isRTL]);

  return {
    isRTL,
    getMarginStart,
    getMarginEnd,
    getPaddingStart,
    getPaddingEnd,
    getBorderStart,
    getBorderEnd,
    getTextAlign,
    getTransformOrigin,
  };
};

/**
 * RTL 图标翻转 Hook
 */
export const useRTLIcon = () => {
  const { isRTL } = useRTL();

  const getIconTransform = useCallback((shouldFlip: boolean = true) => {
    if (!isRTL || !shouldFlip) return {};
    return { transform: 'scaleX(-1)' };
  }, [isRTL]);

  const getRotation = useCallback((degrees: number) => {
    return isRTL ? -degrees : degrees;
  }, [isRTL]);

  return {
    getIconTransform,
    getRotation,
    isRTL,
  };
};

export default useRTL;

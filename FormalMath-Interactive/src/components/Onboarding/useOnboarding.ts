import { useState, useEffect, useCallback } from 'react';

interface OnboardingState {
  hasCompletedTour: boolean;
  hasSkippedTour: boolean;
  lastVisited: string | null;
  visitCount: number;
}

const STORAGE_KEY = 'formalmath-onboarding';

/**
 * 用户引导状态管理Hook
 */
export function useOnboarding() {
  const [state, setState] = useState<OnboardingState>({
    hasCompletedTour: false,
    hasSkippedTour: false,
    lastVisited: null,
    visitCount: 0,
  });
  const [isLoading, setIsLoading] = useState(true);

  // 从localStorage加载状态
  useEffect(() => {
    try {
      const stored = localStorage.getItem(STORAGE_KEY);
      if (stored) {
        setState(JSON.parse(stored));
      }
    } catch (e) {
      console.error('Failed to load onboarding state:', e);
    }
    setIsLoading(false);
  }, []);

  // 保存状态到localStorage
  const saveState = useCallback((newState: Partial<OnboardingState>) => {
    setState(prev => {
      const updated = { ...prev, ...newState };
      try {
        localStorage.setItem(STORAGE_KEY, JSON.stringify(updated));
      } catch (e) {
        console.error('Failed to save onboarding state:', e);
      }
      return updated;
    });
  }, []);

  // 完成引导
  const completeTour = useCallback(() => {
    saveState({
      hasCompletedTour: true,
      hasSkippedTour: false,
      lastVisited: new Date().toISOString(),
    });
  }, [saveState]);

  // 跳过引导
  const skipTour = useCallback(() => {
    saveState({
      hasSkippedTour: true,
      lastVisited: new Date().toISOString(),
    });
  }, [saveState]);

  // 记录访问
  const recordVisit = useCallback(() => {
    setState(prev => {
      const updated = {
        ...prev,
        visitCount: prev.visitCount + 1,
        lastVisited: new Date().toISOString(),
      };
      try {
        localStorage.setItem(STORAGE_KEY, JSON.stringify(updated));
      } catch (e) {
        console.error('Failed to save visit:', e);
      }
      return updated;
    });
  }, []);

  // 重置引导状态
  const resetTour = useCallback(() => {
    saveState({
      hasCompletedTour: false,
      hasSkippedTour: false,
      visitCount: 0,
    });
  }, [saveState]);

  // 是否应该显示引导
  const shouldShowTour = useCallback((): boolean => {
    if (isLoading) return false;
    if (state.hasCompletedTour) return false;
    if (state.hasSkippedTour) {
      // 如果跳过了，7天后可以再次显示
      if (state.lastVisited) {
        const lastVisit = new Date(state.lastVisited);
        const daysSinceLastVisit = (Date.now() - lastVisit.getTime()) / (1000 * 60 * 60 * 24);
        return daysSinceLastVisit >= 7;
      }
    }
    return state.visitCount < 3; // 前3次访问都显示引导
  }, [isLoading, state]);

  return {
    ...state,
    isLoading,
    completeTour,
    skipTour,
    recordVisit,
    resetTour,
    shouldShowTour,
  };
}

/**
 * 检查是否是新用户
 */
export function useIsNewUser(): boolean {
  const [isNew, setIsNew] = useState(false);

  useEffect(() => {
    const hasVisited = localStorage.getItem('formalmath-visited');
    if (!hasVisited) {
      setIsNew(true);
      localStorage.setItem('formalmath-visited', 'true');
    }
  }, []);

  return isNew;
}

/**
 * 功能发现提示管理
 */
interface FeatureTip {
  id: string;
  title: string;
  description: string;
  showCount: number;
  maxShows: number;
}

export function useFeatureTips() {
  const [tips, setTips] = useState<FeatureTip[]>([]);

  useEffect(() => {
    try {
      const stored = localStorage.getItem('formalmath-feature-tips');
      if (stored) {
        setTips(JSON.parse(stored));
      }
    } catch (e) {
      console.error('Failed to load feature tips:', e);
    }
  }, []);

  const saveTips = useCallback((newTips: FeatureTip[]) => {
    setTips(newTips);
    try {
      localStorage.setItem('formalmath-feature-tips', JSON.stringify(newTips));
    } catch (e) {
      console.error('Failed to save feature tips:', e);
    }
  }, []);

  const shouldShowTip = useCallback((tipId: string): boolean => {
    const tip = tips.find(t => t.id === tipId);
    if (!tip) return true; // 新提示默认显示
    return tip.showCount < tip.maxShows;
  }, [tips]);

  const markTipShown = useCallback((tipId: string, title: string, description: string, maxShows = 3) => {
    setTips(prev => {
      const existing = prev.find(t => t.id === tipId);
      let updated: FeatureTip[];
      
      if (existing) {
        updated = prev.map(t => 
          t.id === tipId 
            ? { ...t, showCount: t.showCount + 1 }
            : t
        );
      } else {
        updated = [...prev, { id: tipId, title, description, showCount: 1, maxShows }];
      }
      
      localStorage.setItem('formalmath-feature-tips', JSON.stringify(updated));
      return updated;
    });
  }, []);

  const dismissTip = useCallback((tipId: string) => {
    setTips(prev => {
      const updated = prev.map(t => 
        t.id === tipId 
          ? { ...t, showCount: t.maxShows }
          : t
      );
      localStorage.setItem('formalmath-feature-tips', JSON.stringify(updated));
      return updated;
    });
  }, []);

  return {
    tips,
    shouldShowTip,
    markTipShown,
    dismissTip,
  };
}

export default useOnboarding;

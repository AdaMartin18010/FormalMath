/**
 * A/B测试 React Hooks
 */

import { useState, useEffect, useCallback, useMemo } from 'react';
import {
  ExperimentId,
  VariantId,
  assignVariant,
  getVariantConfig,
  trackExperimentEvent,
  getUserAssignments,
} from './config';

interface UseABTestResult<T> {
  variant: VariantId;
  config: T | undefined;
  track: (event: string, metadata?: Record<string, unknown>) => void;
  isControl: boolean;
}

/**
 * A/B测试 Hook
 * @param experimentId 实验ID
 * @returns 变体信息和追踪函数
 */
export function useABTest<T = Record<string, unknown>>(
  experimentId: ExperimentId
): UseABTestResult<T> {
  const [variant, setVariant] = useState<VariantId>('control');

  useEffect(() => {
    const assigned = assignVariant(experimentId);
    setVariant(assigned);

    // 记录参与事件
    trackExperimentEvent(experimentId, 'participate');
  }, [experimentId]);

  const config = useMemo(() => {
    return getVariantConfig(experimentId) as T | undefined;
  }, [experimentId, variant]);

  const track = useCallback(
    (event: string, metadata?: Record<string, unknown>) => {
      trackExperimentEvent(experimentId, event, metadata);
    },
    [experimentId]
  );

  return {
    variant,
    config,
    track,
    isControl: variant === 'control',
  };
}

/**
 * 多实验Hook
 * 同时管理多个A/B测试
 */
export function useMultipleABTests(experimentIds: ExperimentId[]) {
  const [assignments, setAssignments] = useState<Record<ExperimentId, VariantId>>(
    {} as Record<ExperimentId, VariantId>
  );

  useEffect(() => {
    const newAssignments: Record<ExperimentId, VariantId> = {} as Record<ExperimentId, VariantId>;
    experimentIds.forEach(id => {
      newAssignments[id] = assignVariant(id);
    });
    setAssignments(newAssignments);
  }, [experimentIds]);

  const trackMultiple = useCallback(
    (experimentId: ExperimentId, event: string, metadata?: Record<string, unknown>) => {
      if (assignments[experimentId]) {
        trackExperimentEvent(experimentId, event, metadata);
      }
    },
    [assignments]
  );

  const getConfig = useCallback(
    (experimentId: ExperimentId) => {
      return getVariantConfig(experimentId);
    },
    []
  );

  return {
    assignments,
    track: trackMultiple,
    getConfig,
  };
}

/**
 * A/B测试展示Hook
 * 用于展示不同变体的组件
 */
export function useABTestVariant<T extends Record<string, React.ComponentType<any>>>(
  experimentId: ExperimentId,
  variants: T
): { Component: T[keyof T]; variant: VariantId; track: (event: string) => void } {
  const { variant, track } = useABTest(experimentId);

  const Component = useMemo(() => {
    // 尝试精确匹配变体ID
    if (variants[variant]) {
      return variants[variant];
    }
    // 默认返回control
    return variants['control'] || Object.values(variants)[0];
  }, [variant, variants]);

  return {
    Component,
    variant,
    track,
  };
}

/**
 * A/B测试Hook（服务端渲染安全）
 */
export function useABTestSSR<T = Record<string, unknown>>(
  experimentId: ExperimentId,
  ssrVariant: VariantId = 'control'
): UseABTestResult<T> & { isLoading: boolean } {
  const [isClient, setIsClient] = useState(false);
  
  useEffect(() => {
    setIsClient(true);
  }, []);

  const result = useABTest<T>(experimentId);

  return {
    ...result,
    variant: isClient ? result.variant : ssrVariant,
    isLoading: !isClient,
  };
}

/**
 * 获取所有实验分配Hook
 */
export function useAllABTests() {
  const [assignments, setAssignments] = useState<Record<ExperimentId, VariantId> | null>(null);
  const [isLoading, setIsLoading] = useState(true);

  useEffect(() => {
    const load = () => {
      const all = getUserAssignments();
      setAssignments(all);
      setIsLoading(false);
    };

    load();
  }, []);

  return { assignments, isLoading };
}

export default useABTest;

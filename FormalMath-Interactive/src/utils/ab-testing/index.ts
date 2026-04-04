/**
 * A/B测试工具导出
 */

export { experiments, getUserId, assignVariant, getVariantConfig, trackExperimentEvent, getUserAssignments } from './config';
export type { ExperimentId, VariantId, Variant, Experiment } from './config';

export { useABTest, useMultipleABTests, useABTestVariant, useABTestSSR, useAllABTests } from './hooks';

// 默认导出
export { default } from './config';

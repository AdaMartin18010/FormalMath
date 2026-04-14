// @ts-nocheck
/**
 * 预测分析组件
 * 展示完成预测、性能预测和风险分析
 */

import React, { useState } from 'react';
import * as d3 from 'd3';
import { useD3 } from '@hooks/useD3';
import type { PredictionData, DateProbability, RiskFactor, AtRiskConcept, AdaptiveSuggestion } from '@types/analytics';

interface PredictionAnalysisProps {
  data: PredictionData;
  className?: string;
}

type PredictionView = 'completion' | 'forecast' | 'risk' | 'suggestions';

/**
 * 预测分析组件
 */
export const PredictionAnalysis: React.FC<PredictionAnalysisProps> = ({
  data,
  className = '',
}) => {
  const [activeView, setActiveView] = useState<PredictionView>('completion');

  return (
    <div className={`bg-white dark:bg-slate-800 rounded-xl shadow-lg ${className}`}>
      {/* 头部 */}
      <div className="p-4 border-b border-gray-200 dark:border-slate-700">
        <div className="flex flex-wrap items-center justify-between gap-4">
          <h3 className="text-lg font-semibold text-gray-800 dark:text-gray-200">预测分析</h3>

          {/* 视图切换 */}
          <div className="flex bg-gray-100 dark:bg-slate-700 rounded-lg p-1">
            {[
              { key: 'completion', label: '完成预测' },
              { key: 'forecast', label: '性能预测' },
              { key: 'risk', label: '风险分析' },
              { key: 'suggestions', label: '自适应建议' },
            ].map((view) => (
              <button
                key={view.key}
                onClick={() => setActiveView(view.key as PredictionView)}
                className={`px-3 py-1.5 text-sm rounded-md transition-colors ${
                  activeView === view.key
                    ? 'bg-white dark:bg-slate-600 text-blue-600 dark:text-blue-400 shadow-sm'
                    : 'text-gray-600 dark:text-gray-400 hover:text-gray-900 dark:hover:text-gray-200'
                }`}
              >
                {view.label}
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* 内容区域 */}
      <div className="p-4">
        {activeView === 'completion' && <CompletionView data={data.completionPrediction} />}
        {activeView === 'forecast' && <ForecastView data={data.performanceForecast} />}
        {activeView === 'risk' && <RiskView data={data.riskAnalysis} />}
        {activeView === 'suggestions' && <SuggestionsView data={data.adaptiveSuggestions} />}
      </div>
    </div>
  );
};

// 完成预测视图
const CompletionView: React.FC<{ data: PredictionData['completionPrediction'] }> = ({ data }) => {
  const svgRef = useD3(
    (svg) => {
      if (data.probabilityByDate.length === 0) return;

      const margin = { top: 20, right: 30, bottom: 50, left: 50 };
      const width = 600 - margin.left - margin.right;
      const height = 250 - margin.top - margin.bottom;

      svg.selectAll('*').remove();

      const g = svg
        .attr('width', width + margin.left + margin.right)
        .attr('height', height + margin.top + margin.bottom)
        .append('g')
        .attr('transform', `translate(${margin.left},${margin.top})`);

      // 解析日期
      const parseDate = d3.timeParse('%Y-%m-%d');
      const chartData = data.probabilityByDate.map((d) => ({
        ...d,
        date: parseDate(d.date) as Date,
      }));

      // 比例尺
      const x = d3.scaleTime()
        .domain(d3.extent(chartData, (d) => d.date) as [Date, Date])
        .range([0, width]);

      const y = d3.scaleLinear().domain([0, 100]).nice().range([height, 0]);

      // 区域生成器
      const area = d3
        .area<DateProbability & { date: Date }>()
        .x((d) => x(d.date))
        .y0(height)
        .y1((d) => y(d.probability))
        .curve(d3.curveMonotoneX);

      // 线条生成器
      const line = d3
        .line<DateProbability & { date: Date }>()
        .x((d) => x(d.date))
        .y((d) => y(d.probability))
        .curve(d3.curveMonotoneX);

      // 渐变
      const defs = svg.append('defs');
      const gradient = defs
        .append('linearGradient')
        .attr('id', 'predictionGradient')
        .attr('x1', '0%')
        .attr('y1', '0%')
        .attr('x2', '0%')
        .attr('y2', '100%');
      gradient.append('stop').attr('offset', '0%').attr('stop-color', '#3b82f6').attr('stop-opacity', 0.4);
      gradient.append('stop').attr('offset', '100%').attr('stop-color', '#3b82f6').attr('stop-opacity', 0.05);

      // 绘制区域
      g.append('path')
        .datum(chartData)
        .attr('fill', 'url(#predictionGradient)')
        .attr('d', area);

      // 绘制线条
      g.append('path')
        .datum(chartData)
        .attr('fill', 'none')
        .attr('stroke', '#3b82f6')
        .attr('stroke-width', 2)
        .attr('d', line);

      // X轴
      g.append('g')
        .attr('transform', `translate(0,${height})`)
        .call(d3.axisBottom(x).tickFormat(d3.timeFormat('%m/%d') as any))
        .style('color', '#6b7280');

      // Y轴
      g.append('g').call(d3.axisLeft(y).ticks(5).tickFormat((d) => `${d}%`)).style('color', '#6b7280');

      // 目标线 (90%)
      g.append('line')
        .attr('x1', 0)
        .attr('x2', width)
        .attr('y1', y(90))
        .attr('y2', y(90))
        .attr('stroke', '#22c55e')
        .attr('stroke-width', 1)
        .attr('stroke-dasharray', '5,5');

      g.append('text')
        .attr('x', width - 5)
        .attr('y', y(90) - 5)
        .attr('text-anchor', 'end')
        .style('font-size', '10px')
        .style('fill', '#22c55e')
        .text('90% 目标');
    },
    [data.probabilityByDate]
  );

  return (
    <div className="space-y-4">
      {/* 预测结果 */}
      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <PredictionCard
          label="预计完成日期"
          value={new Date(data.targetCompletionDate).toLocaleDateString('zh-CN')}
          type="primary"
        />
        <PredictionCard
          label="乐观估计"
          value={new Date(data.confidenceInterval.optimistic).toLocaleDateString('zh-CN')}
          type="success"
        />
        <PredictionCard
          label="保守估计"
          value={new Date(data.confidenceInterval.pessimistic).toLocaleDateString('zh-CN')}
          type="warning"
        />
      </div>

      {/* 影响因子 */}
      <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
        <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">预测影响因素</h4>
        <div className="space-y-2">
          {data.factors.map((factor, index) => (
            <div key={index} className="flex items-center justify-between py-2 border-b border-gray-200 dark:border-slate-600 last:border-0">
              <span className="text-sm text-gray-700 dark:text-gray-300">{factor.name}</span>
              <div className="flex items-center gap-3">
                <span
                  className={`text-sm font-medium ${
                    factor.impact > 0
                      ? 'text-green-600 dark:text-green-400'
                      : factor.impact < 0
                      ? 'text-red-600 dark:text-red-400'
                      : 'text-gray-600 dark:text-gray-400'
                  }`}
                >
                  {factor.impact > 0 ? '+' : ''}{factor.impact}
                </span>
                <span
                  className={`text-xs px-2 py-0.5 rounded ${
                    factor.trend === 'positive'
                      ? 'bg-green-100 text-green-700 dark:bg-green-900/30 dark:text-green-400'
                      : factor.trend === 'negative'
                      ? 'bg-red-100 text-red-700 dark:bg-red-900/30 dark:text-red-400'
                      : 'bg-gray-100 text-gray-700 dark:bg-slate-600 dark:text-gray-400'
                  }`}
                >
                  {factor.trend === 'positive' ? '↑ 积极' : factor.trend === 'negative' ? '↓ 消极' : '→ 稳定'}
                </span>
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* 概率曲线 */}
      <div>
        <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">完成概率预测</h4>
        <div className="overflow-x-auto">
          <svg ref={svgRef} />
        </div>
      </div>
    </div>
  );
};

// 预测卡片
const PredictionCard: React.FC<{
  label: string;
  value: string;
  type: 'primary' | 'success' | 'warning';
}> = ({ label, value, type }) => {
  const colors = {
    primary: 'bg-blue-50 border-blue-200 dark:bg-blue-900/20 dark:border-blue-800',
    success: 'bg-green-50 border-green-200 dark:bg-green-900/20 dark:border-green-800',
    warning: 'bg-orange-50 border-orange-200 dark:bg-orange-900/20 dark:border-orange-800',
  };

  return (
    <div className={`rounded-lg p-4 border ${colors[type]}`}>
      <div className="text-xs text-gray-500 dark:text-gray-400 mb-1">{label}</div>
      <div className="text-lg font-bold text-gray-800 dark:text-gray-200">{value}</div>
    </div>
  );
};

// 性能预测视图
const ForecastView: React.FC<{ data: PredictionData['performanceForecast'] }> = ({ data }) => {
  return (
    <div className="space-y-6">
      {/* 下周预测 */}
      <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
        <div className="flex items-center justify-between mb-3">
          <h4 className="font-medium text-gray-800 dark:text-gray-200">下周预测</h4>
          <span className="text-xs text-gray-500 dark:text-gray-400">
            置信度: {Math.round(data.nextWeek.confidence * 100)}%
          </span>
        </div>
        <div className="grid grid-cols-2 gap-4">
          <div className="bg-white dark:bg-slate-600 rounded-lg p-3">
            <div className="text-2xl font-bold text-blue-600 dark:text-blue-400">
              {data.nextWeek.expectedConcepts}
            </div>
            <div className="text-xs text-gray-500 dark:text-gray-400">预计掌握概念</div>
          </div>
          <div className="bg-white dark:bg-slate-600 rounded-lg p-3">
            <div className="text-2xl font-bold text-green-600 dark:text-green-400">
              +{data.nextWeek.expectedMasteryGain}%
            </div>
            <div className="text-xs text-gray-500 dark:text-gray-400">掌握度增长</div>
          </div>
        </div>
      </div>

      {/* 下月预测 */}
      <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
        <div className="flex items-center justify-between mb-3">
          <h4 className="font-medium text-gray-800 dark:text-gray-200">下月预测</h4>
          <span className="text-xs text-gray-500 dark:text-gray-400">
            置信度: {Math.round(data.nextMonth.confidence * 100)}%
          </span>
        </div>
        <div className="grid grid-cols-2 gap-4 mb-3">
          <div className="bg-white dark:bg-slate-600 rounded-lg p-3">
            <div className="text-2xl font-bold text-blue-600 dark:text-blue-400">
              {data.nextMonth.expectedConcepts}
            </div>
            <div className="text-xs text-gray-500 dark:text-gray-400">预计掌握概念</div>
          </div>
          <div className="bg-white dark:bg-slate-600 rounded-lg p-3">
            <div className="text-2xl font-bold text-green-600 dark:text-green-400">
              +{data.nextMonth.expectedMasteryGain}%
            </div>
            <div className="text-xs text-gray-500 dark:text-gray-400">掌握度增长</div>
          </div>
        </div>
        {data.nextMonth.milestones.length > 0 && (
          <div className="text-sm text-gray-600 dark:text-gray-400">
            <span className="font-medium">预期里程碑: </span>
            {data.nextMonth.milestones.join(', ')}
          </div>
        )}
      </div>

      {/* 趋势预测 */}
      <div>
        <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">能力维度趋势预测</h4>
        <div className="space-y-2">
          {data.trends.map((trend, index) => (
            <div key={index} className="flex items-center justify-between py-2">
              <span className="text-sm text-gray-700 dark:text-gray-300">{trend.metric}</span>
              <div className="flex items-center gap-4">
                <span className="text-sm text-gray-500 dark:text-gray-400">当前: {trend.current}</span>
                <span className="text-sm text-blue-600 dark:text-blue-400">预测: {trend.predicted}</span>
                <span
                  className={`text-sm font-medium ${
                    trend.change > 0
                      ? 'text-green-600 dark:text-green-400'
                      : trend.change < 0
                      ? 'text-red-600 dark:text-red-400'
                      : 'text-gray-600 dark:text-gray-400'
                  }`}
                >
                  {trend.change > 0 ? '↗' : trend.change < 0 ? '↘' : '→'} {Math.abs(trend.change)}
                </span>
              </div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

// 风险分析视图
const RiskView: React.FC<{ data: PredictionData['riskAnalysis'] }> = ({ data }) => {
  const getRiskColor = (risk: RiskFactor['severity']) => {
    const colors: Record<string, string> = {
      low: 'bg-green-100 text-green-700 dark:bg-green-900/30 dark:text-green-400',
      medium: 'bg-yellow-100 text-yellow-700 dark:bg-yellow-900/30 dark:text-yellow-400',
      high: 'bg-red-100 text-red-700 dark:bg-red-900/30 dark:text-red-400',
    };
    return colors[risk] || colors.low;
  };

  const getOverallRiskColor = (risk: PredictionData['riskAnalysis']['overallRisk']) => {
    const colors: Record<string, string> = {
      low: 'text-green-600 dark:text-green-400',
      medium: 'text-yellow-600 dark:text-yellow-400',
      high: 'text-red-600 dark:text-red-400',
    };
    return colors[risk] || colors.low;
  };

  return (
    <div className="space-y-6">
      {/* 总体风险 */}
      <div className="text-center py-4 bg-gray-50 dark:bg-slate-700 rounded-lg">
        <div className="text-sm text-gray-500 dark:text-gray-400 mb-1">总体风险等级</div>
        <div className={`text-3xl font-bold ${getOverallRiskColor(data.overallRisk)}`}>
          {data.overallRisk === 'low' ? '低风险' : data.overallRisk === 'medium' ? '中风险' : '高风险'}
        </div>
      </div>

      {/* 风险因子 */}
      {data.riskFactors.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">风险因素</h4>
          <div className="space-y-2">
            {data.riskFactors.map((factor, index) => (
              <div key={index} className="bg-gray-50 dark:bg-slate-700 rounded-lg p-3">
                <div className="flex items-center justify-between">
                  <div className="flex items-center gap-2">
                    <span
                      className={`text-xs px-2 py-0.5 rounded ${getRiskColor(factor.severity)}`}
                    >
                      {factor.severity === 'high' ? '高' : factor.severity === 'medium' ? '中' : '低'}
                    </span>
                    <span className="font-medium text-gray-800 dark:text-gray-200">
                      {factor.type === 'engagement' ? '参与度' : factor.type === 'difficulty' ? '难度' : factor.type === 'time' ? '时间' : '前置知识'}
                    </span>
                  </div>
                  <span className="text-sm text-gray-500 dark:text-gray-400">
                    概率: {Math.round(factor.probability * 100)}%
                  </span>
                </div>
                <p className="text-sm text-gray-600 dark:text-gray-400 mt-1">{factor.description}</p>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 风险概念 */}
      {data.atRiskConcepts.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">需要关注的概念</h4>
          <div className="space-y-2">
            {data.atRiskConcepts.map((concept) => (
              <div key={concept.conceptId} className="flex items-center justify-between py-2 border-b border-gray-200 dark:border-slate-700 last:border-0">
                <span className="text-sm text-gray-700 dark:text-gray-300">{concept.conceptName}</span>
                <div className="flex items-center gap-2">
                  <span className={`text-xs px-2 py-0.5 rounded ${getRiskColor(concept.riskLevel)}`}>
                    {concept.riskLevel === 'high' ? '高风险' : concept.riskLevel === 'medium' ? '中风险' : '低风险'}
                  </span>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 缓解策略 */}
      {data.mitigationStrategies.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">缓解策略</h4>
          <div className="space-y-2">
            {data.mitigationStrategies.map((strategy, index) => (
              <div
                key={index}
                className={`rounded-lg p-3 border-l-4 ${
                  strategy.priority === 'high'
                    ? 'bg-red-50 border-red-500 dark:bg-red-900/20 dark:border-red-400'
                    : strategy.priority === 'medium'
                    ? 'bg-yellow-50 border-yellow-500 dark:bg-yellow-900/20 dark:border-yellow-400'
                    : 'bg-blue-50 border-blue-500 dark:bg-blue-900/20 dark:border-blue-400'
                }`}
              >
                <div className="font-medium text-gray-800 dark:text-gray-200">{strategy.action}</div>
                <div className="text-sm text-gray-600 dark:text-gray-400 mt-1">
                  针对: {strategy.targetRisk}
                </div>
                <div className="text-xs text-green-600 dark:text-green-400 mt-1">
                  预期效果: {strategy.expectedEffect}
                </div>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

// 自适应建议视图
const SuggestionsView: React.FC<{ data: AdaptiveSuggestion[] }> = ({ data }) => {
  const getTypeIcon = (type: AdaptiveSuggestion['type']) => {
    const icons: Record<string, string> = {
      pace: '⏱️',
      content: '📚',
      schedule: '📅',
      method: '🔧',
    };
    return icons[type] || '💡';
  };

  const getTypeLabel = (type: AdaptiveSuggestion['type']) => {
    const labels: Record<string, string> = {
      pace: '学习节奏',
      content: '学习内容',
      schedule: '学习计划',
      method: '学习方法',
    };
    return labels[type] || type;
  };

  return (
    <div className="space-y-4">
      <p className="text-sm text-gray-600 dark:text-gray-400">
        根据您的学习数据分析，我们为您提供以下个性化建议，帮助您优化学习效果。
      </p>

      <div className="space-y-3">
        {data.map((suggestion) => (
          <div key={suggestion.id} className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
            <div className="flex items-start gap-3">
              <span className="text-2xl">{getTypeIcon(suggestion.type)}</span>
              <div className="flex-1">
                <div className="flex items-center gap-2">
                  <span className="text-xs px-2 py-0.5 bg-blue-100 text-blue-700 dark:bg-blue-900/30 dark:text-blue-400 rounded">
                    {getTypeLabel(suggestion.type)}
                  </span>
                </div>
                
                <div className="mt-2 grid grid-cols-1 md:grid-cols-2 gap-3">
                  <div className="bg-white dark:bg-slate-600 rounded p-2">
                    <div className="text-xs text-gray-500 dark:text-gray-400">当前</div>
                    <div className="text-sm text-gray-700 dark:text-gray-300">{suggestion.current}</div>
                  </div>
                  <div className="bg-green-50 dark:bg-green-900/20 rounded p-2">
                    <div className="text-xs text-green-600 dark:text-green-400">建议</div>
                    <div className="text-sm text-green-700 dark:text-green-300">{suggestion.suggested}</div>
                  </div>
                </div>

                <div className="mt-2 text-sm text-gray-600 dark:text-gray-400">
                  <span className="font-medium">原因: </span>{suggestion.reason}
                </div>
                <div className="mt-1 text-xs text-green-600 dark:text-green-400">
                  <span className="font-medium">预期收益: </span>{suggestion.expectedBenefit}
                </div>
              </div>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
};

export default PredictionAnalysis;

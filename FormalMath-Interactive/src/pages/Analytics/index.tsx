// @ts-nocheck
/**
 * FormalMath 数据分析仪表板页面（优化版）
 * 
 * 新增功能：
 * - 实时数据更新
 * - 优化的图表交互体验
 * - 数据导出功能
 * - 自定义报表
 * - 移动端适配
 */

import React, { useEffect, useState, useCallback, useMemo } from 'react';
import { useRealtimeAnalytics } from '@hooks/useRealtimeAnalytics';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';
import { 
  ProgressDashboard, 
  MasteryHeatmap, 
  EfficiencyAnalysis, 
  KnowledgeNetwork, 
  PredictionAnalysis,
  ExportPanel,
  CustomReportBuilder,
  RealtimeIndicator,
} from './components';
import type {
  LearningProgressData,
  MasteryHeatmapData,
  EfficiencyAnalysisData,
  KnowledgeNetworkData,
  PredictionData,
} from '@types/analytics';
import { 
  Download, RefreshCw, Filter, LayoutGrid, 
  Settings, ChevronLeft, ChevronRight, Menu, X,
  FileText, BarChart3, PieChart, TrendingUp, Network, Sparkles
} from 'lucide-react';

type DashboardSection = 'progress' | 'heatmap' | 'efficiency' | 'network' | 'prediction';

// ==================== 模拟数据生成器 ====================

const generateMockData = (userId: string) => {
  const now = new Date().toISOString();
  
  const progressData: LearningProgressData = {
    userId,
    generatedAt: now,
    summary: {
      totalConcepts: 150,
      masteredConcepts: 45,
      inProgressConcepts: 32,
      notStartedConcepts: 73,
      overallProgress: 30,
      averageMastery: 42,
      totalTimeSpent: 3600,
      weeklyStudyTime: 480,
      dailyAverage: 68,
    },
    trends: Array.from({ length: 30 }, (_, i) => ({
      date: new Date(Date.now() - (29 - i) * 24 * 60 * 60 * 1000).toISOString().split('T')[0],
      conceptsLearned: Math.floor(Math.random() * 3),
      conceptsMastered: Math.floor(Math.random() * 2),
      timeSpent: Math.floor(Math.random() * 120) + 30,
      masteryGrowth: Math.random() * 5,
    })),
    milestones: [
      {
        id: '1',
        title: '基础概念掌握',
        description: '完成数学基础概念的学习',
        targetConcepts: 50,
        completedConcepts: 45,
        progress: 90,
        deadline: new Date(Date.now() + 7 * 24 * 60 * 60 * 1000).toISOString(),
        status: 'in_progress',
      },
      {
        id: '2',
        title: '定理证明入门',
        description: '掌握基本定理的证明方法',
        targetConcepts: 30,
        completedConcepts: 12,
        progress: 40,
        deadline: new Date(Date.now() + 30 * 24 * 60 * 60 * 1000).toISOString(),
        status: 'in_progress',
      },
    ],
    goals: [
      {
        id: '1',
        title: '每日学习目标',
        description: '每天至少学习2个新概念',
        targetValue: 2,
        currentValue: 1.5,
        unit: '概念/天',
        progress: 75,
        status: 'active',
      },
    ],
  };

  const categories = [
    { id: 'algebra', name: '代数', color: '#3b82f6', conceptCount: 40 },
    { id: 'geometry', name: '几何', color: '#22c55e', conceptCount: 35 },
    { id: 'analysis', name: '分析', color: '#f59e0b', conceptCount: 30 },
    { id: 'logic', name: '逻辑', color: '#ef4444', conceptCount: 25 },
  ];

  const cells = categories.flatMap((cat, catIdx) => 
    Array.from({ length: cat.conceptCount }, (_, i) => ({
      conceptId: `${cat.id}-${i}`,
      conceptName: `${cat.name}概念${i + 1}`,
      categoryId: cat.id,
      masteryLevel: Math.floor(Math.random() * 100),
      masteryLabel: '未开始' as const,
      lastStudiedAt: Math.random() > 0.5 ? new Date(Date.now() - Math.random() * 7 * 24 * 60 * 60 * 1000).toISOString() : undefined,
      studyCount: Math.floor(Math.random() * 10),
      timeSpent: Math.floor(Math.random() * 300),
      x: i % 10,
      y: Math.floor(i / 10) + catIdx * 4,
    }))
  );

  const heatmapData: MasteryHeatmapData = {
    userId,
    generatedAt: now,
    categories,
    cells,
    overallStats: {
      averageMastery: 42,
      masteryDistribution: { notStarted: 73, beginner: 25, intermediate: 32, advanced: 15, master: 5 },
      weakestCategory: '分析',
      strongestCategory: '代数',
      needsReview: cells.filter(c => c.masteryLevel > 0 && c.masteryLevel < 30).slice(0, 5).map(c => c.conceptId),
    },
  };

  const efficiencyData: EfficiencyAnalysisData = {
    userId,
    generatedAt: now,
    overallEfficiency: 72,
    timeDistribution: {
      byHour: Array.from({ length: 24 }, (_, i) => ({
        hour: i,
        avgEfficiency: [8, 9, 10, 11].includes(i) ? 85 : [14, 15, 16].includes(i) ? 78 : [19, 20, 21].includes(i) ? 82 : Math.random() * 60 + 20,
        avgTimeSpent: Math.floor(Math.random() * 60),
        conceptsLearned: Math.floor(Math.random() * 5),
      })),
      byDayOfWeek: [
        { day: 0, dayName: '周日', avgEfficiency: 65, totalTimeSpent: 120, conceptsLearned: 3 },
        { day: 1, dayName: '周一', avgEfficiency: 80, totalTimeSpent: 180, conceptsLearned: 5 },
        { day: 2, dayName: '周二', avgEfficiency: 85, totalTimeSpent: 200, conceptsLearned: 6 },
        { day: 3, dayName: '周三', avgEfficiency: 78, totalTimeSpent: 160, conceptsLearned: 4 },
        { day: 4, dayName: '周四', avgEfficiency: 82, totalTimeSpent: 190, conceptsLearned: 5 },
        { day: 5, dayName: '周五', avgEfficiency: 70, totalTimeSpent: 140, conceptsLearned: 3 },
        { day: 6, dayName: '周六', avgEfficiency: 75, totalTimeSpent: 200, conceptsLearned: 5 },
      ],
      bySessionLength: [
        { range: '0-30min', avgEfficiency: 55, sessionCount: 20, conceptsPerHour: 2 },
        { range: '30-60min', avgEfficiency: 75, sessionCount: 35, conceptsPerHour: 3 },
        { range: '1-2h', avgEfficiency: 85, sessionCount: 25, conceptsPerHour: 4 },
        { range: '2h+', avgEfficiency: 70, sessionCount: 10, conceptsPerHour: 3 },
      ],
    },
    learningPatterns: [
      { id: '1', name: '晨间学习', description: '上午9-11点学习效率最高', frequency: 5, avgEfficiency: 88, trend: 'improving' },
    ],
    optimalConditions: [
      { factor: '学习时段', optimalValue: '上午9-11点', impact: 15, confidence: 0.85 },
    ],
    recommendations: [
      { id: '1', type: 'schedule', title: '调整学习时间', description: '将重要概念学习安排在上午9-11点', expectedImprovement: 15, priority: 'high' },
    ],
  };

  const networkData: KnowledgeNetworkData = {
    userId,
    generatedAt: now,
    nodes: Array.from({ length: 50 }, (_, i) => ({
      id: `node-${i}`,
      conceptId: `concept-${i}`,
      label: `概念${i + 1}`,
      category: categories[i % 4].name,
      masteryLevel: Math.floor(Math.random() * 100),
      importance: Math.random(),
      connections: Math.floor(Math.random() * 10) + 1,
      x: Math.random() * 800,
      y: Math.random() * 500,
      size: Math.random() * 15 + 10,
      color: categories[i % 4].color,
    })),
    edges: Array.from({ length: 80 }, (_, i) => ({
      source: `node-${Math.floor(Math.random() * 50)}`,
      target: `node-${Math.floor(Math.random() * 50)}`,
      type: ['prerequisite', 'related', 'extension'][Math.floor(Math.random() * 3)] as KnowledgeNetworkData['edges'][0]['type'],
      strength: Math.random(),
      userKnown: Math.random() > 0.5,
    })).filter(e => e.source !== e.target),
    networkStats: {
      totalNodes: 50,
      totalEdges: 80,
      density: 0.065,
      averageDegree: 3.2,
      clusteringCoefficient: 0.42,
      connectedComponents: 3,
      knowledgeCoverage: 0.35,
    },
    communities: categories.map((cat, i) => ({
      id: cat.id,
      name: cat.name,
      conceptIds: Array.from({ length: cat.conceptCount }, (_, j) => `concept-${i * 10 + j}`),
      avgMastery: Math.floor(Math.random() * 40) + 30,
      cohesion: Math.random() * 0.4 + 0.5,
      color: cat.color,
    })),
    bridges: [
      { conceptId: 'concept-5', conceptName: '函数', betweenness: 0.85, connectsCommunities: ['代数', '分析'], importance: 'critical' },
      { conceptId: 'concept-15', conceptName: '证明方法', betweenness: 0.72, connectsCommunities: ['逻辑', '几何'], importance: 'important' },
    ],
  };

  const predictionData: PredictionData = {
    userId,
    generatedAt: now,
    completionPrediction: {
      targetCompletionDate: new Date(Date.now() + 180 * 24 * 60 * 60 * 1000).toISOString(),
      confidenceInterval: {
        optimistic: new Date(Date.now() + 150 * 24 * 60 * 60 * 1000).toISOString(),
        pessimistic: new Date(Date.now() + 220 * 24 * 60 * 60 * 1000).toISOString(),
      },
      probabilityByDate: Array.from({ length: 30 }, (_, i) => ({
        date: new Date(Date.now() + (i + 1) * 7 * 24 * 60 * 60 * 1000).toISOString().split('T')[0],
        probability: Math.min(100, (i + 1) * 3.5 + 20),
      })),
      factors: [
        { name: '学习连贯性', impact: 15, trend: 'positive' },
        { name: '学习时长', impact: 10, trend: 'positive' },
        { name: '复习频率', impact: 8, trend: 'neutral' },
        { name: '难度分布', impact: -5, trend: 'negative' },
      ],
    },
    performanceForecast: {
      nextWeek: { expectedConcepts: 8, expectedMasteryGain: 5, confidence: 0.82 },
      nextMonth: { expectedConcepts: 35, expectedMasteryGain: 18, milestones: ['基础概念掌握'], confidence: 0.75 },
      trends: [
        { metric: '知识掌握度', current: 42, predicted: 48, change: 6 },
        { metric: '问题解决能力', current: 38, predicted: 45, change: 7 },
        { metric: '证明能力', current: 25, predicted: 32, change: 7 },
      ],
    },
    riskAnalysis: {
      overallRisk: 'medium',
      riskFactors: [
        { type: 'time', severity: 'medium', description: '最近一周学习时间有所下降', probability: 0.6 },
      ],
      atRiskConcepts: [
        { conceptId: 'c1', conceptName: '实数完备性', riskLevel: 'medium', reason: '前置概念掌握不足' },
      ],
      mitigationStrategies: [
        { targetRisk: '学习时间下降', action: '设置每日学习提醒', expectedEffect: '提高学习规律性', priority: 'high' },
      ],
    },
    adaptiveSuggestions: [
      { id: '1', type: 'pace', current: '每天学习1-2小时', suggested: '改为每天45分钟，分两次', reason: '短时高频学习效果更好', expectedBenefit: '效率提升15%' },
      { id: '2', type: 'content', current: '线性推进', suggested: '增加交叉复习', reason: '间隔重复有助于长期记忆', expectedBenefit: '记忆保持率提升20%' },
      { id: '3', type: 'schedule', current: '晚上学习', suggested: '调整为上午学习', reason: '认知能力在上午更强', expectedBenefit: '理解速度提升25%' },
    ],
  };

  return { progressData, heatmapData, efficiencyData, networkData, predictionData };
};

// ==================== 主组件 ====================

const AnalyticsPage: React.FC = () => {
  const [activeSection, setActiveSection] = useState<DashboardSection>('progress');
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [showExportPanel, setShowExportPanel] = useState(false);
  const [showCustomReport, setShowCustomReport] = useState(false);
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);
  
  // 检测移动端
  const { isMobile, isTablet } = useMobileDetect();
  const isSmallScreen = isMobile || isTablet;
  
  // 数据状态
  const [progressData, setProgressData] = useState<LearningProgressData | null>(null);
  const [heatmapData, setHeatmapData] = useState<MasteryHeatmapData | null>(null);
  const [efficiencyData, setEfficiencyData] = useState<EfficiencyAnalysisData | null>(null);
  const [networkData, setNetworkData] = useState<KnowledgeNetworkData | null>(null);
  const [predictionData, setPredictionData] = useState<PredictionData | null>(null);
  
  // 实时数据（模拟）
  const { lastUpdate, isConnected, connectionStatus, refresh } = useRealtimeAnalytics('user-1', {
    enabled: true,
    interval: 30000,
  });

  // 加载数据
  const loadData = useCallback(async () => {
    setLoading(true);
    setError(null);

    try {
      const mock = generateMockData('user-1');
      await new Promise(resolve => setTimeout(resolve, 800));

      setProgressData(mock.progressData);
      setHeatmapData(mock.heatmapData);
      setEfficiencyData(mock.efficiencyData);
      setNetworkData(mock.networkData);
      setPredictionData(mock.predictionData);
    } catch (err) {
      setError(err instanceof Error ? err.message : '加载数据失败');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    loadData();
  }, [loadData]);

  // 导航配置
  const sections = useMemo(() => [
    { key: 'progress' as DashboardSection, label: '学习进度', icon: BarChart3, color: 'blue' },
    { key: 'heatmap' as DashboardSection, label: '掌握热力图', icon: PieChart, color: 'orange' },
    { key: 'efficiency' as DashboardSection, label: '效率分析', icon: TrendingUp, color: 'green' },
    { key: 'network' as DashboardSection, label: '知识网络', icon: Network, color: 'purple' },
    { key: 'prediction' as DashboardSection, label: '预测分析', icon: Sparkles, color: 'pink' },
  ], []);

  // 渲染内容
  const renderContent = () => {
    if (loading) {
      return (
        <div className="flex items-center justify-center h-64">
          <RefreshCw className="w-8 h-8 text-blue-600 animate-spin" />
          <span className="ml-3 text-gray-600 dark:text-gray-400">加载分析数据...</span>
        </div>
      );
    }

    if (error) {
      return (
        <div className="text-center py-12">
          <div className="text-red-600 dark:text-red-400 mb-4">{error}</div>
          <button
            onClick={loadData}
            className="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
          >
            重试
          </button>
        </div>
      );
    }

    return (
      <div className="space-y-6 animate-fadeIn">
        {activeSection === 'progress' && progressData && (
          <ProgressDashboard 
            data={progressData} 
            onMilestoneClick={(m) => console.log('Milestone:', m)}
            onGoalClick={(g) => console.log('Goal:', g)}
          />
        )}
        {activeSection === 'heatmap' && heatmapData && (
          <MasteryHeatmap 
            data={heatmapData} 
            onCellClick={(c) => console.log('Cell:', c)}
          />
        )}
        {activeSection === 'efficiency' && efficiencyData && (
          <EfficiencyAnalysis data={efficiencyData} />
        )}
        {activeSection === 'network' && networkData && (
          <KnowledgeNetwork 
            data={networkData} 
            onNodeClick={(n) => console.log('Node:', n)}
          />
        )}
        {activeSection === 'prediction' && predictionData && (
          <PredictionAnalysis data={predictionData} />
        )}
      </div>
    );
  };

  // 移动端底部导航
  const MobileNav = () => (
    <div className="fixed bottom-0 left-0 right-0 bg-white dark:bg-slate-800 border-t border-gray-200 dark:border-slate-700 z-40">
      <div className="flex justify-around p-2">
        {sections.map((section) => {
          const Icon = section.icon;
          const isActive = activeSection === section.key;
          return (
            <button
              key={section.key}
              onClick={() => setActiveSection(section.key)}
              className={`flex flex-col items-center p-2 rounded-lg transition-colors ${
                isActive 
                  ? `text-${section.color}-600 bg-${section.color}-50 dark:bg-${section.color}-900/20` 
                  : 'text-gray-500 dark:text-gray-400'
              }`}
            >
              <Icon className="w-5 h-5" />
              <span className="text-xs mt-1">{section.label.slice(0, 2)}</span>
            </button>
          );
        })}
      </div>
    </div>
  );

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-slate-900 pb-20 md:pb-6">
      {/* 顶部导航栏 - 移动端优化 */}
      <header className="sticky top-0 z-30 bg-white/80 dark:bg-slate-800/80 backdrop-blur-md border-b border-gray-200 dark:border-slate-700">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="flex items-center justify-between h-16">
            {/* 左侧：标题 */}
            <div className="flex items-center gap-3">
              {isSmallScreen && (
                <button
                  onClick={() => setMobileMenuOpen(!mobileMenuOpen)}
                  className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg"
                >
                  {mobileMenuOpen ? <X className="w-5 h-5" /> : <Menu className="w-5 h-5" />}
                </button>
              )}
              <div>
                <h1 className="text-lg sm:text-xl font-bold text-gray-900 dark:text-white">
                  数据分析仪表板
                </h1>
                <p className="hidden sm:block text-xs text-gray-500 dark:text-gray-400">
                  深入了解您的学习进度和效率
                </p>
              </div>
            </div>

            {/* 右侧：操作按钮 */}
            <div className="flex items-center gap-2">
              {/* 实时状态指示器 - 桌面端显示 */}
              {!isSmallScreen && (
                <RealtimeIndicator
                  isConnected={isConnected}
                  lastUpdate={lastUpdate}
                  connectionStatus={connectionStatus}
                  onRefresh={refresh}
                  isRefreshing={loading}
                />
              )}

              <button
                onClick={() => setShowCustomReport(true)}
                className="flex items-center gap-1.5 px-3 py-2 text-sm font-medium text-gray-700 
                         dark:text-gray-300 bg-white dark:bg-slate-700 border border-gray-300 
                         dark:border-slate-600 rounded-lg hover:bg-gray-50 dark:hover:bg-slate-600
                         transition-colors"
              >
                <LayoutGrid className="w-4 h-4" />
                <span className="hidden sm:inline">自定义报表</span>
              </button>

              <button
                onClick={() => setShowExportPanel(true)}
                className="flex items-center gap-1.5 px-3 py-2 text-sm font-medium text-white 
                         bg-blue-600 rounded-lg hover:bg-blue-700 transition-colors"
              >
                <Download className="w-4 h-4" />
                <span className="hidden sm:inline">导出</span>
              </button>
            </div>
          </div>
        </div>

        {/* 移动端菜单 */}
        {isSmallScreen && mobileMenuOpen && (
          <div className="border-t border-gray-200 dark:border-slate-700 bg-white dark:bg-slate-800">
            <div className="px-4 py-3">
              <RealtimeIndicator
                isConnected={isConnected}
                lastUpdate={lastUpdate}
                connectionStatus={connectionStatus}
                onRefresh={refresh}
                isRefreshing={loading}
              />
            </div>
          </div>
        )}
      </header>

      {/* 桌面端导航标签 */}
      {!isSmallScreen && (
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-4">
          <div className="flex gap-2 overflow-x-auto pb-2 scrollbar-hide">
            {sections.map((section) => {
              const Icon = section.icon;
              const isActive = activeSection === section.key;
              return (
                <button
                  key={section.key}
                  onClick={() => setActiveSection(section.key)}
                  className={`flex items-center gap-2 px-4 py-2.5 rounded-lg font-medium 
                           whitespace-nowrap transition-all ${
                    isActive
                      ? 'bg-blue-600 text-white shadow-md shadow-blue-600/20'
                      : 'bg-white dark:bg-slate-800 text-gray-700 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-slate-700'
                  }`}
                >
                  <Icon className="w-4 h-4" />
                  {section.label}
                </button>
              );
            })}
          </div>
        </div>
      )}

      {/* 主内容区 */}
      <main className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-4">
        {renderContent()}
      </main>

      {/* 移动端底部导航 */}
      {isSmallScreen && <MobileNav />}

      {/* 导出面板 */}
      {showExportPanel && (
        <ExportPanel
          data={{ progress: progressData, heatmap: heatmapData, efficiency: efficiencyData, network: networkData, prediction: predictionData }}
          onClose={() => setShowExportPanel(false)}
        />
      )}

      {/* 自定义报表构建器 */}
      {showCustomReport && (
        <CustomReportBuilder onClose={() => setShowCustomReport(false)} />
      )}

      {/* 添加全局动画样式 */}
      <style>{`
        @keyframes fadeIn {
          from { opacity: 0; transform: translateY(10px); }
          to { opacity: 1; transform: translateY(0); }
        }
        .animate-fadeIn {
          animation: fadeIn 0.3s ease-out;
        }
        .scrollbar-hide::-webkit-scrollbar {
          display: none;
        }
        .scrollbar-hide {
          -ms-overflow-style: none;
          scrollbar-width: none;
        }
      `}</style>
    </div>
  );
};

export default AnalyticsPage;

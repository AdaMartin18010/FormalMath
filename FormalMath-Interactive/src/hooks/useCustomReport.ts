/**
 * 自定义报表 Hook
 * 支持创建、保存和生成自定义报表
 */

import { useState, useCallback, useEffect } from 'react';
import type { TimeRange, DateRange } from '@types/analytics';

export type ReportWidgetType = 
  | 'progress-summary'
  | 'progress-trends'
  | 'progress-milestones'
  | 'heatmap-overview'
  | 'heatmap-cells'
  | 'heatmap-stats'
  | 'efficiency-overview'
  | 'efficiency-hourly'
  | 'efficiency-weekly'
  | 'efficiency-patterns'
  | 'network-graph'
  | 'network-communities'
  | 'network-bridges'
  | 'network-stats'
  | 'prediction-completion'
  | 'prediction-forecast'
  | 'prediction-risk'
  | 'prediction-suggestions';

export interface ReportWidget {
  id: string;
  type: ReportWidgetType;
  title: string;
  position: { x: number; y: number; w: number; h: number };
  config?: Record<string, unknown>;
}

export interface CustomReport {
  id: string;
  name: string;
  description?: string;
  widgets: ReportWidget[];
  timeRange: TimeRange;
  dateRange?: DateRange;
  createdAt: string;
  updatedAt: string;
  isDefault?: boolean;
  isPublic?: boolean;
}

export interface ReportTemplate {
  id: string;
  name: string;
  description: string;
  icon: string;
  widgets: Omit<ReportWidget, 'id'>[];
  defaultTimeRange: TimeRange;
}

interface UseCustomReportReturn {
  reports: CustomReport[];
  currentReport: CustomReport | null;
  templates: ReportTemplate[];
  createReport: (name: string, templateId?: string) => CustomReport;
  updateReport: (reportId: string, updates: Partial<CustomReport>) => void;
  deleteReport: (reportId: string) => void;
  loadReport: (reportId: string) => void;
  addWidget: (reportId: string, widget: Omit<ReportWidget, 'id'>) => void;
  removeWidget: (reportId: string, widgetId: string) => void;
  updateWidget: (reportId: string, widgetId: string, updates: Partial<ReportWidget>) => void;
  duplicateReport: (reportId: string, newName?: string) => CustomReport;
  exportReport: (reportId: string) => string;
  importReport: (jsonString: string) => CustomReport | null;
  saveToLocalStorage: () => void;
  loadFromLocalStorage: () => void;
}

// 预定义报表模板
const DEFAULT_TEMPLATES: ReportTemplate[] = [
  {
    id: 'learning-overview',
    name: '学习概览',
    description: '展示学习进度、掌握度和效率的综合概览',
    icon: '📊',
    defaultTimeRange: 'month',
    widgets: [
      { type: 'progress-summary', title: '学习进度总览', position: { x: 0, y: 0, w: 2, h: 2 } },
      { type: 'progress-trends', title: '学习趋势', position: { x: 2, y: 0, w: 2, h: 2 } },
      { type: 'heatmap-overview', title: '概念掌握情况', position: { x: 0, y: 2, w: 2, h: 2 } },
      { type: 'efficiency-overview', title: '学习效率', position: { x: 2, y: 2, w: 2, h: 2 } },
    ],
  },
  {
    id: 'detailed-analysis',
    name: '详细分析',
    description: '深入分析学习时间、模式和知识网络',
    icon: '🔍',
    defaultTimeRange: 'month',
    widgets: [
      { type: 'efficiency-hourly', title: '时段效率分析', position: { x: 0, y: 0, w: 3, h: 2 } },
      { type: 'efficiency-weekly', title: '星期效率分析', position: { x: 3, y: 0, w: 1, h: 2 } },
      { type: 'network-graph', title: '知识网络', position: { x: 0, y: 2, w: 2, h: 3 } },
      { type: 'network-communities', title: '知识社群', position: { x: 2, y: 2, w: 2, h: 3 } },
      { type: 'efficiency-patterns', title: '学习模式', position: { x: 0, y: 5, w: 4, h: 2 } },
    ],
  },
  {
    id: 'goal-tracking',
    name: '目标追踪',
    description: '追踪里程碑、目标完成情况和预测',
    icon: '🎯',
    defaultTimeRange: 'quarter',
    widgets: [
      { type: 'progress-milestones', title: '里程碑进度', position: { x: 0, y: 0, w: 2, h: 3 } },
      { type: 'prediction-completion', title: '完成预测', position: { x: 2, y: 0, w: 2, h: 2 } },
      { type: 'prediction-forecast', title: '性能预测', position: { x: 2, y: 2, w: 2, h: 2 } },
      { type: 'prediction-risk', title: '风险分析', position: { x: 0, y: 3, w: 2, h: 2 } },
      { type: 'prediction-suggestions', title: '改进建议', position: { x: 2, y: 4, w: 2, h: 2 } },
    ],
  },
  {
    id: 'mastery-focus',
    name: '掌握度聚焦',
    description: '专注于概念掌握情况和需要复习的内容',
    icon: '🎓',
    defaultTimeRange: 'week',
    widgets: [
      { type: 'heatmap-cells', title: '概念掌握详情', position: { x: 0, y: 0, w: 3, h: 3 } },
      { type: 'heatmap-stats', title: '掌握度统计', position: { x: 3, y: 0, w: 1, h: 3 } },
      { type: 'network-bridges', title: '关键概念', position: { x: 0, y: 3, w: 2, h: 2 } },
      { type: 'progress-summary', title: '进度摘要', position: { x: 2, y: 3, w: 2, h: 2 } },
    ],
  },
];

// 生成唯一 ID
const generateId = () => `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

// LocalStorage 键名
const STORAGE_KEY = 'formalmath-custom-reports';

/**
 * 自定义报表 Hook
 */
export function useCustomReport(): UseCustomReportReturn {
  const [reports, setReports] = useState<CustomReport[]>([]);
  const [currentReport, setCurrentReport] = useState<CustomReport | null>(null);
  const templates = DEFAULT_TEMPLATES;

  // 从 LocalStorage 加载
  const loadFromLocalStorage = useCallback(() => {
    try {
      const stored = localStorage.getItem(STORAGE_KEY);
      if (stored) {
        const parsed = JSON.parse(stored);
        setReports(parsed.reports || []);
        if (parsed.currentReportId) {
          const report = parsed.reports?.find((r: CustomReport) => r.id === parsed.currentReportId);
          if (report) {
            setCurrentReport(report);
          }
        }
      }
    } catch (err) {
      console.error('加载自定义报表失败:', err);
    }
  }, []);

  // 保存到 LocalStorage
  const saveToLocalStorage = useCallback(() => {
    try {
      const data = {
        reports,
        currentReportId: currentReport?.id,
      };
      localStorage.setItem(STORAGE_KEY, JSON.stringify(data));
    } catch (err) {
      console.error('保存自定义报表失败:', err);
    }
  }, [reports, currentReport]);

  // 初始化时加载
  useEffect(() => {
    loadFromLocalStorage();
  }, [loadFromLocalStorage]);

  // 创建新报表
  const createReport = useCallback((name: string, templateId?: string): CustomReport => {
    const now = new Date().toISOString();
    let widgets: ReportWidget[] = [];
    let timeRange: TimeRange = 'month';

    // 如果使用模板
    if (templateId) {
      const template = templates.find(t => t.id === templateId);
      if (template) {
        widgets = template.widgets.map(w => ({
          ...w,
          id: generateId(),
        }));
        timeRange = template.defaultTimeRange;
      }
    }

    const newReport: CustomReport = {
      id: generateId(),
      name,
      widgets,
      timeRange,
      createdAt: now,
      updatedAt: now,
    };

    setReports(prev => [...prev, newReport]);
    setCurrentReport(newReport);
    return newReport;
  }, [templates]);

  // 更新报表
  const updateReport = useCallback((reportId: string, updates: Partial<CustomReport>) => {
    setReports(prev =>
      prev.map(report =>
        report.id === reportId
          ? { ...report, ...updates, updatedAt: new Date().toISOString() }
          : report
      )
    );
    
    if (currentReport?.id === reportId) {
      setCurrentReport(prev => prev ? { ...prev, ...updates, updatedAt: new Date().toISOString() } : null);
    }
  }, [currentReport]);

  // 删除报表
  const deleteReport = useCallback((reportId: string) => {
    setReports(prev => prev.filter(r => r.id !== reportId));
    if (currentReport?.id === reportId) {
      setCurrentReport(null);
    }
  }, [currentReport]);

  // 加载报表
  const loadReport = useCallback((reportId: string) => {
    const report = reports.find(r => r.id === reportId);
    if (report) {
      setCurrentReport(report);
    }
  }, [reports]);

  // 添加组件
  const addWidget = useCallback((reportId: string, widget: Omit<ReportWidget, 'id'>) => {
    const newWidget: ReportWidget = {
      ...widget,
      id: generateId(),
    };

    setReports(prev =>
      prev.map(report =>
        report.id === reportId
          ? { ...report, widgets: [...report.widgets, newWidget], updatedAt: new Date().toISOString() }
          : report
      )
    );

    if (currentReport?.id === reportId) {
      setCurrentReport(prev =>
        prev ? { ...prev, widgets: [...prev.widgets, newWidget], updatedAt: new Date().toISOString() } : null
      );
    }
  }, [currentReport]);

  // 移除组件
  const removeWidget = useCallback((reportId: string, widgetId: string) => {
    setReports(prev =>
      prev.map(report =>
        report.id === reportId
          ? { ...report, widgets: report.widgets.filter(w => w.id !== widgetId), updatedAt: new Date().toISOString() }
          : report
      )
    );

    if (currentReport?.id === reportId) {
      setCurrentReport(prev =>
        prev ? { ...prev, widgets: prev.widgets.filter(w => w.id !== widgetId), updatedAt: new Date().toISOString() } : null
      );
    }
  }, [currentReport]);

  // 更新组件
  const updateWidget = useCallback((reportId: string, widgetId: string, updates: Partial<ReportWidget>) => {
    setReports(prev =>
      prev.map(report =>
        report.id === reportId
          ? {
              ...report,
              widgets: report.widgets.map(w =>
                w.id === widgetId ? { ...w, ...updates } : w
              ),
              updatedAt: new Date().toISOString(),
            }
          : report
      )
    );

    if (currentReport?.id === reportId) {
      setCurrentReport(prev =>
        prev
          ? {
              ...prev,
              widgets: prev.widgets.map(w =>
                w.id === widgetId ? { ...w, ...updates } : w
              ),
              updatedAt: new Date().toISOString(),
            }
          : null
      );
    }
  }, [currentReport]);

  // 复制报表
  const duplicateReport = useCallback((reportId: string, newName?: string): CustomReport => {
    const report = reports.find(r => r.id === reportId);
    if (!report) throw new Error('报表不存在');

    const now = new Date().toISOString();
    const duplicated: CustomReport = {
      ...report,
      id: generateId(),
      name: newName || `${report.name} (副本)`,
      widgets: report.widgets.map(w => ({ ...w, id: generateId() })),
      createdAt: now,
      updatedAt: now,
    };

    setReports(prev => [...prev, duplicated]);
    setCurrentReport(duplicated);
    return duplicated;
  }, [reports]);

  // 导出报表为 JSON
  const exportReport = useCallback((reportId: string): string => {
    const report = reports.find(r => r.id === reportId);
    if (!report) throw new Error('报表不存在');

    return JSON.stringify(report, null, 2);
  }, [reports]);

  // 导入报表
  const importReport = useCallback((jsonString: string): CustomReport | null => {
    try {
      const imported = JSON.parse(jsonString) as CustomReport;
      const now = new Date().toISOString();
      
      const newReport: CustomReport = {
        ...imported,
        id: generateId(),
        name: `${imported.name} (导入)`,
        widgets: imported.widgets.map(w => ({ ...w, id: generateId() })),
        createdAt: now,
        updatedAt: now,
      };

      setReports(prev => [...prev, newReport]);
      setCurrentReport(newReport);
      return newReport;
    } catch (err) {
      console.error('导入报表失败:', err);
      return null;
    }
  }, []);

  return {
    reports,
    currentReport,
    templates,
    createReport,
    updateReport,
    deleteReport,
    loadReport,
    addWidget,
    removeWidget,
    updateWidget,
    duplicateReport,
    exportReport,
    importReport,
    saveToLocalStorage,
    loadFromLocalStorage,
  };
}

export default useCustomReport;

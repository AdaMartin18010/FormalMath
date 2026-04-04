/**
 * 自定义报表构建器组件
 * 允许用户创建和配置自定义数据分析报表
 */

import React, { useState } from 'react';
import { useCustomReport, type ReportWidgetType, type ReportTemplate } from '@hooks/useCustomReport';
import { 
  Plus, X, LayoutGrid, Save, Copy, Trash2, Download, Upload, 
  Settings, ChevronDown, GripVertical, Edit3 
} from 'lucide-react';

interface CustomReportBuilderProps {
  onClose?: () => void;
}

const WIDGET_TYPES: { type: ReportWidgetType; label: string; category: string; icon: string }[] = [
  // 进度相关
  { type: 'progress-summary', label: '进度总览', category: '学习进度', icon: '📊' },
  { type: 'progress-trends', label: '趋势图表', category: '学习进度', icon: '📈' },
  { type: 'progress-milestones', label: '里程碑', category: '学习进度', icon: '🏆' },
  
  // 热力图相关
  { type: 'heatmap-overview', label: '热力图概览', category: '概念掌握', icon: '🔥' },
  { type: 'heatmap-cells', label: '概念详情', category: '概念掌握', icon: '📋' },
  { type: 'heatmap-stats', label: '掌握度统计', category: '概念掌握', icon: '📉' },
  
  // 效率相关
  { type: 'efficiency-overview', label: '效率总览', category: '学习效率', icon: '⚡' },
  { type: 'efficiency-hourly', label: '时段分析', category: '学习效率', icon: '🕐' },
  { type: 'efficiency-weekly', label: '星期分析', category: '学习效率', icon: '📅' },
  { type: 'efficiency-patterns', label: '学习模式', category: '学习效率', icon: '🔄' },
  
  // 网络相关
  { type: 'network-graph', label: '网络图', category: '知识网络', icon: '🕸️' },
  { type: 'network-communities', label: '知识社群', category: '知识网络', icon: '👥' },
  { type: 'network-bridges', label: '关键概念', category: '知识网络', icon: '🔗' },
  { type: 'network-stats', label: '网络统计', category: '知识网络', icon: '📐' },
  
  // 预测相关
  { type: 'prediction-completion', label: '完成预测', category: '预测分析', icon: '🎯' },
  { type: 'prediction-forecast', label: '性能预测', category: '预测分析', icon: '🔮' },
  { type: 'prediction-risk', label: '风险分析', category: '预测分析', icon: '⚠️' },
  { type: 'prediction-suggestions', label: '改进建议', category: '预测分析', icon: '💡' },
];

export const CustomReportBuilder: React.FC<CustomReportBuilderProps> = ({ onClose }) => {
  const {
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
  } = useCustomReport();

  const [showTemplates, setShowTemplates] = useState(false);
  const [showWidgetPanel, setShowWidgetPanel] = useState(false);
  const [editingReport, setEditingReport] = useState(false);
  const [reportName, setReportName] = useState('');
  const [selectedCategory, setSelectedCategory] = useState<string | null>(null);

  // 从模板创建
  const handleCreateFromTemplate = (template: ReportTemplate) => {
    createReport(template.name, template.id);
    setShowTemplates(false);
  };

  // 创建空白报表
  const handleCreateBlank = () => {
    createReport('新报表');
    setShowTemplates(false);
  };

  // 保存报表
  const handleSave = () => {
    saveToLocalStorage();
    alert('报表已保存');
  };

  // 导出当前报表
  const handleExport = () => {
    if (!currentReport) return;
    const json = exportReport(currentReport.id);
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `${currentReport.name}.json`;
    a.click();
    URL.revokeObjectURL(url);
  };

  // 导入报表
  const handleImport = (event: React.ChangeEvent<HTMLInputElement>) => {
    const file = event.target.files?.[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (e) => {
      const content = e.target?.result as string;
      importReport(content);
    };
    reader.readAsText(file);
  };

  // 更新报表名称
  const handleUpdateName = () => {
    if (currentReport && reportName.trim()) {
      updateReport(currentReport.id, { name: reportName.trim() });
      setEditingReport(false);
    }
  };

  // 添加组件到报表
  const handleAddWidget = (type: ReportWidgetType) => {
    if (!currentReport) return;
    
    const widgetType = WIDGET_TYPES.find(w => w.type === type);
    if (!widgetType) return;

    // 计算新组件的位置（简单的自动布局）
    const y = Math.max(0, ...currentReport.widgets.map(w => w.position.y + w.position.h));
    
    addWidget(currentReport.id, {
      type,
      title: widgetType.label,
      position: { x: 0, y, w: 2, h: 2 },
    });
    
    setShowWidgetPanel(false);
  };

  // 按分类分组组件类型
  const groupedWidgets = WIDGET_TYPES.reduce((acc, widget) => {
    if (!acc[widget.category]) {
      acc[widget.category] = [];
    }
    acc[widget.category].push(widget);
    return acc;
  }, {} as Record<string, typeof WIDGET_TYPES>);

  return (
    <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50 p-4">
      <div className="bg-white dark:bg-slate-800 rounded-xl shadow-2xl w-full max-w-6xl h-[90vh] flex flex-col">
        {/* 头部 */}
        <div className="flex items-center justify-between p-4 border-b border-gray-200 dark:border-slate-700">
          <div className="flex items-center gap-4">
            <div className="flex items-center gap-2">
              <LayoutGrid className="w-6 h-6 text-blue-600" />
              {editingReport && currentReport ? (
                <div className="flex items-center gap-2">
                  <input
                    type="text"
                    value={reportName}
                    onChange={(e) => setReportName(e.target.value)}
                    onBlur={handleUpdateName}
                    onKeyDown={(e) => e.key === 'Enter' && handleUpdateName()}
                    autoFocus
                    className="px-2 py-1 border border-blue-500 rounded text-lg font-semibold
                             bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
                  />
                </div>
              ) : currentReport ? (
                <div className="flex items-center gap-2">
                  <h2 className="text-xl font-semibold text-gray-900 dark:text-white">
                    {currentReport.name}
                  </h2>
                  <button
                    onClick={() => {
                      setReportName(currentReport.name);
                      setEditingReport(true);
                    }}
                    className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded"
                  >
                    <Edit3 className="w-4 h-4 text-gray-400" />
                  </button>
                </div>
              ) : (
                <h2 className="text-xl font-semibold text-gray-900 dark:text-white">自定义报表</h2>
              )}
            </div>
          </div>

          <div className="flex items-center gap-2">
            {currentReport && (
              <>
                <button
                  onClick={handleSave}
                  className="flex items-center gap-1 px-3 py-2 text-sm font-medium text-gray-700 
                           dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg"
                >
                  <Save className="w-4 h-4" />
                  保存
                </button>
                <button
                  onClick={handleExport}
                  className="flex items-center gap-1 px-3 py-2 text-sm font-medium text-gray-700 
                           dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg"
                >
                  <Download className="w-4 h-4" />
                  导出
                </button>
                <label className="flex items-center gap-1 px-3 py-2 text-sm font-medium text-gray-700 
                               dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg cursor-pointer">
                  <Upload className="w-4 h-4" />
                  导入
                  <input type="file" accept=".json" onChange={handleImport} className="hidden" />
                </label>
              </>
            )}
            <button
              onClick={onClose}
              className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg"
            >
              <X className="w-5 h-5 text-gray-500" />
            </button>
          </div>
        </div>

        <div className="flex-1 flex overflow-hidden">
          {/* 左侧：报表列表 */}
          <div className="w-64 border-r border-gray-200 dark:border-slate-700 flex flex-col">
            <div className="p-4 border-b border-gray-200 dark:border-slate-700">
              <button
                onClick={() => setShowTemplates(!showTemplates)}
                className="w-full flex items-center justify-center gap-2 px-4 py-2 
                         bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
              >
                <Plus className="w-4 h-4" />
                新建报表
              </button>

              {/* 模板选择 */}
              {showTemplates && (
                <div className="mt-3 p-3 bg-gray-50 dark:bg-slate-700 rounded-lg space-y-2">
                  <p className="text-xs font-medium text-gray-500 dark:text-gray-400">从模板创建</p>
                  {templates.map((template) => (
                    <button
                      key={template.id}
                      onClick={() => handleCreateFromTemplate(template)}
                      className="w-full text-left p-2 hover:bg-white dark:hover:bg-slate-600 rounded 
                               transition-colors"
                    >
                      <div className="flex items-center gap-2">
                        <span>{template.icon}</span>
                        <span className="text-sm font-medium text-gray-700 dark:text-gray-300">
                          {template.name}
                        </span>
                      </div>
                      <p className="text-xs text-gray-500 mt-1">{template.description}</p>
                    </button>
                  ))}
                  <div className="border-t border-gray-200 dark:border-slate-600 pt-2">
                    <button
                      onClick={handleCreateBlank}
                      className="w-full text-left p-2 hover:bg-white dark:hover:bg-slate-600 rounded"
                    >
                      <span className="text-sm text-gray-600 dark:text-gray-400">创建空白报表</span>
                    </button>
                  </div>
                </div>
              )}
            </div>

            {/* 报表列表 */}
            <div className="flex-1 overflow-auto p-4">
              <p className="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">我的报表</p>
              <div className="space-y-2">
                {reports.map((report) => (
                  <div
                    key={report.id}
                    onClick={() => loadReport(report.id)}
                    className={`p-3 rounded-lg cursor-pointer transition-colors ${
                      currentReport?.id === report.id
                        ? 'bg-blue-50 dark:bg-blue-900/20 border border-blue-200 dark:border-blue-800'
                        : 'hover:bg-gray-50 dark:hover:bg-slate-700'
                    }`}
                  >
                    <div className="flex items-start justify-between">
                      <span className="text-sm font-medium text-gray-700 dark:text-gray-300">
                        {report.name}
                      </span>
                      {currentReport?.id === report.id && (
                        <div className="flex gap-1">
                          <button
                            onClick={(e) => {
                              e.stopPropagation();
                              duplicateReport(report.id);
                            }}
                            className="p-1 hover:bg-gray-200 dark:hover:bg-slate-600 rounded"
                          >
                            <Copy className="w-3 h-3 text-gray-400" />
                          </button>
                          <button
                            onClick={(e) => {
                              e.stopPropagation();
                              if (confirm('确定要删除这个报表吗？')) {
                                deleteReport(report.id);
                              }
                            }}
                            className="p-1 hover:bg-red-100 dark:hover:bg-red-900/30 rounded"
                          >
                            <Trash2 className="w-3 h-3 text-red-400" />
                          </button>
                        </div>
                      )}
                    </div>
                    <p className="text-xs text-gray-400 mt-1">
                      {report.widgets.length} 个组件 · {new Date(report.updatedAt).toLocaleDateString('zh-CN')}
                    </p>
                  </div>
                ))}
                {reports.length === 0 && (
                  <p className="text-sm text-gray-400 text-center py-4">暂无自定义报表</p>
                )}
              </div>
            </div>
          </div>

          {/* 中间：报表编辑区 */}
          <div className="flex-1 flex flex-col">
            {currentReport ? (
              <>
                {/* 工具栏 */}
                <div className="p-4 border-b border-gray-200 dark:border-slate-700 flex items-center justify-between">
                  <div className="flex items-center gap-4">
                    <select
                      value={currentReport.timeRange}
                      onChange={(e) => updateReport(currentReport.id, { timeRange: e.target.value as any })}
                      className="px-3 py-1.5 text-sm border border-gray-300 dark:border-slate-600 
                               rounded-lg bg-white dark:bg-slate-700 text-gray-700 dark:text-gray-300"
                    >
                      <option value="day">今天</option>
                      <option value="week">本周</option>
                      <option value="month">本月</option>
                      <option value="quarter">本季度</option>
                      <option value="year">本年</option>
                    </select>
                  </div>
                  <button
                    onClick={() => setShowWidgetPanel(!showWidgetPanel)}
                    className="flex items-center gap-2 px-4 py-2 text-sm font-medium text-blue-600 
                             bg-blue-50 dark:bg-blue-900/20 rounded-lg hover:bg-blue-100 dark:hover:bg-blue-900/30"
                  >
                    <Plus className="w-4 h-4" />
                    添加组件
                  </button>
                </div>

                {/* 组件面板 */}
                {showWidgetPanel && (
                  <div className="absolute right-4 top-32 w-80 bg-white dark:bg-slate-800 rounded-xl 
                               shadow-2xl border border-gray-200 dark:border-slate-700 z-10 max-h-[60vh] overflow-auto">
                    <div className="p-4 border-b border-gray-200 dark:border-slate-700 flex items-center justify-between">
                      <h3 className="font-medium text-gray-900 dark:text-white">添加组件</h3>
                      <button onClick={() => setShowWidgetPanel(false)}>
                        <X className="w-4 h-4 text-gray-400" />
                      </button>
                    </div>
                    <div className="p-4 space-y-4">
                      {Object.entries(groupedWidgets).map(([category, widgets]) => (
                        <div key={category}>
                          <p className="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">
                            {category}
                          </p>
                          <div className="grid grid-cols-2 gap-2">
                            {widgets.map((widget) => (
                              <button
                                key={widget.type}
                                onClick={() => handleAddWidget(widget.type)}
                                className="flex items-center gap-2 p-2 text-left hover:bg-gray-50 
                                         dark:hover:bg-slate-700 rounded-lg transition-colors"
                              >
                                <span>{widget.icon}</span>
                                <span className="text-sm text-gray-700 dark:text-gray-300">
                                  {widget.label}
                                </span>
                              </button>
                            ))}
                          </div>
                        </div>
                      ))}
                    </div>
                  </div>
                )}

                {/* 报表画布 */}
                <div className="flex-1 p-6 overflow-auto bg-gray-50 dark:bg-slate-900">
                  {currentReport.widgets.length === 0 ? (
                    <div className="h-full flex flex-col items-center justify-center text-gray-400">
                      <LayoutGrid className="w-16 h-16 mb-4 opacity-50" />
                      <p>点击"添加组件"开始构建报表</p>
                    </div>
                  ) : (
                    <div className="grid grid-cols-4 gap-4 auto-rows-min">
                      {currentReport.widgets.map((widget, index) => (
                        <div
                          key={widget.id}
                          className={`bg-white dark:bg-slate-800 rounded-xl shadow-sm border 
                                   border-gray-200 dark:border-slate-700 overflow-hidden
                                   ${widget.position.w === 2 ? 'col-span-2' : ''}
                                   ${widget.position.w === 3 ? 'col-span-3' : ''}
                                   ${widget.position.w === 4 ? 'col-span-4' : ''}`}
                          style={{ minHeight: `${widget.position.h * 100}px` }}
                        >
                          <div className="flex items-center justify-between p-3 border-b 
                                        border-gray-100 dark:border-slate-700">
                            <div className="flex items-center gap-2">
                              <GripVertical className="w-4 h-4 text-gray-300 cursor-move" />
                              <span className="font-medium text-gray-700 dark:text-gray-300">
                                {widget.title}
                              </span>
                            </div>
                            <button
                              onClick={() => removeWidget(currentReport.id, widget.id)}
                              className="p-1 hover:bg-red-50 dark:hover:bg-red-900/20 rounded"
                            >
                              <X className="w-4 h-4 text-gray-400 hover:text-red-500" />
                            </button>
                          </div>
                          <div className="p-4 flex items-center justify-center text-gray-400 min-h-[100px]">
                            <p className="text-sm">组件预览: {widget.type}</p>
                          </div>
                        </div>
                      ))}
                    </div>
                  )}
                </div>
              </>
            ) : (
              <div className="flex-1 flex items-center justify-center text-gray-400">
                <div className="text-center">
                  <LayoutGrid className="w-16 h-16 mx-auto mb-4 opacity-50" />
                  <p>选择一个报表或创建新报表</p>
                </div>
              </div>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

export default CustomReportBuilder;

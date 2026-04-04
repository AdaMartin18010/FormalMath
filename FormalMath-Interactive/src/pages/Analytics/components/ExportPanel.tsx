/**
 * 数据导出面板组件
 * 支持多种格式导出数据分析结果
 */

import React, { useState } from 'react';
import { useDataExport, type ExportFormat, type ExportSection } from '@hooks/useDataExport';
import type {
  LearningProgressData,
  MasteryHeatmapData,
  EfficiencyAnalysisData,
  KnowledgeNetworkData,
  PredictionData,
} from '@types/analytics';
import { Download, FileSpreadsheet, FileJson, FileText, FileCode, X, Check, Loader2 } from 'lucide-react';

interface ExportPanelProps {
  data: {
    progress?: LearningProgressData;
    heatmap?: MasteryHeatmapData;
    efficiency?: EfficiencyAnalysisData;
    network?: KnowledgeNetworkData;
    prediction?: PredictionData;
  };
  onClose?: () => void;
}

const FORMAT_OPTIONS: { value: ExportFormat; label: string; icon: React.ReactNode; description: string }[] = [
  { value: 'csv', label: 'CSV', icon: <FileSpreadsheet className="w-5 h-5" />, description: '表格数据，适合 Excel 分析' },
  { value: 'json', label: 'JSON', icon: <FileCode className="w-5 h-5" />, description: '结构化数据，适合开发' },
  { value: 'excel', label: 'Excel', icon: <FileSpreadsheet className="w-5 h-5" />, description: 'Excel 电子表格' },
  { value: 'pdf', label: 'PDF', icon: <FileText className="w-5 h-5" />, description: '可打印的 PDF 报告' },
];

const SECTION_OPTIONS: { value: ExportSection; label: string; description: string }[] = [
  { value: 'progress', label: '学习进度', description: '进度统计、趋势、里程碑和目标' },
  { value: 'heatmap', label: '掌握热力图', description: '概念掌握程度和分类统计' },
  { value: 'efficiency', label: '效率分析', description: '时间分布、模式和优化建议' },
  { value: 'network', label: '知识网络', description: '知识图谱、社群和关键概念' },
  { value: 'prediction', label: '预测分析', description: '完成预测、性能预测和风险分析' },
  { value: 'all', label: '完整报告', description: '包含所有分析数据' },
];

export const ExportPanel: React.FC<ExportPanelProps> = ({ data, onClose }) => {
  const { isExporting, progress, exportData } = useDataExport();
  const [selectedFormat, setSelectedFormat] = useState<ExportFormat>('csv');
  const [selectedSection, setSelectedSection] = useState<ExportSection>('all');
  const [customFilename, setCustomFilename] = useState('');
  const [exportResult, setExportResult] = useState<{ success: boolean; message: string } | null>(null);

  const handleExport = async () => {
    setExportResult(null);
    
    const result = await exportData(data, {
      format: selectedFormat,
      section: selectedSection,
      filename: customFilename || undefined,
    });

    if (result.success) {
      setExportResult({ success: true, message: `导出成功: ${result.filename}` });
    } else {
      setExportResult({ success: false, message: result.error || '导出失败' });
    }
  };

  return (
    <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50 p-4">
      <div className="bg-white dark:bg-slate-800 rounded-xl shadow-2xl max-w-lg w-full max-h-[90vh] overflow-auto">
        {/* 头部 */}
        <div className="flex items-center justify-between p-4 border-b border-gray-200 dark:border-slate-700">
          <div className="flex items-center gap-2">
            <Download className="w-5 h-5 text-blue-600" />
            <h2 className="text-lg font-semibold text-gray-900 dark:text-white">导出数据</h2>
          </div>
          <button
            onClick={onClose}
            className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors"
          >
            <X className="w-5 h-5 text-gray-500" />
          </button>
        </div>

        <div className="p-4 space-y-6">
          {/* 导出格式选择 */}
          <div>
            <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">
              选择导出格式
            </label>
            <div className="grid grid-cols-2 gap-3">
              {FORMAT_OPTIONS.map((format) => (
                <button
                  key={format.value}
                  onClick={() => setSelectedFormat(format.value)}
                  className={`flex items-start gap-3 p-3 rounded-lg border-2 transition-all text-left ${
                    selectedFormat === format.value
                      ? 'border-blue-500 bg-blue-50 dark:bg-blue-900/20'
                      : 'border-gray-200 dark:border-slate-600 hover:border-gray-300 dark:hover:border-slate-500'
                  }`}
                >
                  <div className={`${selectedFormat === format.value ? 'text-blue-600' : 'text-gray-500'}`}>
                    {format.icon}
                  </div>
                  <div>
                    <div className={`font-medium ${selectedFormat === format.value ? 'text-blue-900 dark:text-blue-100' : 'text-gray-900 dark:text-gray-100'}`}>
                      {format.label}
                    </div>
                    <div className="text-xs text-gray-500 dark:text-gray-400 mt-0.5">
                      {format.description}
                    </div>
                  </div>
                </button>
              ))}
            </div>
          </div>

          {/* 数据范围选择 */}
          <div>
            <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">
              选择导出内容
            </label>
            <div className="space-y-2">
              {SECTION_OPTIONS.map((section) => (
                <button
                  key={section.value}
                  onClick={() => setSelectedSection(section.value)}
                  className={`w-full flex items-center justify-between p-3 rounded-lg border transition-all ${
                    selectedSection === section.value
                      ? 'border-blue-500 bg-blue-50 dark:bg-blue-900/20'
                      : 'border-gray-200 dark:border-slate-600 hover:border-gray-300 dark:hover:border-slate-500'
                  }`}
                >
                  <div className="text-left">
                    <div className={`font-medium ${selectedSection === section.value ? 'text-blue-900 dark:text-blue-100' : 'text-gray-900 dark:text-gray-100'}`}>
                      {section.label}
                    </div>
                    <div className="text-xs text-gray-500 dark:text-gray-400">
                      {section.description}
                    </div>
                  </div>
                  {selectedSection === section.value && (
                    <Check className="w-5 h-5 text-blue-600" />
                  )}
                </button>
              ))}
            </div>
          </div>

          {/* 文件名 */}
          <div>
            <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">
              文件名（可选）
            </label>
            <input
              type="text"
              value={customFilename}
              onChange={(e) => setCustomFilename(e.target.value)}
              placeholder={`formalmath-analytics-${selectedSection}-${new Date().toISOString().split('T')[0]}`}
              className="w-full px-3 py-2 border border-gray-300 dark:border-slate-600 rounded-lg 
                       bg-white dark:bg-slate-700 text-gray-900 dark:text-white
                       focus:outline-none focus:ring-2 focus:ring-blue-500"
            />
          </div>

          {/* 导出结果 */}
          {exportResult && (
            <div
              className={`p-3 rounded-lg ${
                exportResult.success
                  ? 'bg-green-50 dark:bg-green-900/20 text-green-700 dark:text-green-300'
                  : 'bg-red-50 dark:bg-red-900/20 text-red-700 dark:text-red-300'
              }`}
            >
              {exportResult.message}
            </div>
          )}

          {/* 导出按钮 */}
          <button
            onClick={handleExport}
            disabled={isExporting}
            className="w-full flex items-center justify-center gap-2 px-4 py-3 
                     bg-blue-600 text-white rounded-lg font-medium
                     hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed
                     transition-colors"
          >
            {isExporting ? (
              <>
                <Loader2 className="w-5 h-5 animate-spin" />
                导出中... {progress}%
              </>
            ) : (
              <>
                <Download className="w-5 h-5" />
                导出数据
              </>
            )}
          </button>
        </div>
      </div>
    </div>
  );
};

export default ExportPanel;

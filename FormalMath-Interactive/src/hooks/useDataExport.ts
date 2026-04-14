// @ts-nocheck
/**
 * 数据导出 Hook
 * 支持 CSV、JSON、PDF 导出
 */

import { useState, useCallback } from 'react';
import type {
  LearningProgressData,
  MasteryHeatmapData,
  EfficiencyAnalysisData,
  KnowledgeNetworkData,
  PredictionData,
} from '@types/analytics';

export type ExportFormat = 'csv' | 'json' | 'pdf' | 'excel';
export type ExportSection = 'progress' | 'heatmap' | 'efficiency' | 'network' | 'prediction' | 'all';

interface ExportOptions {
  format: ExportFormat;
  section: ExportSection;
  filename?: string;
  dateRange?: { start: Date; end: Date };
}

interface ExportResult {
  success: boolean;
  url?: string;
  blob?: Blob;
  filename: string;
  error?: string;
}

interface UseDataExportReturn {
  isExporting: boolean;
  progress: number;
  exportData: (data: AnalyticsData, options: ExportOptions) => Promise<ExportResult>;
  exportToCSV: (data: unknown[], filename: string) => void;
  exportToJSON: (data: unknown, filename: string) => void;
  downloadFile: (blob: Blob, filename: string) => void;
}

interface AnalyticsData {
  progress?: LearningProgressData;
  heatmap?: MasteryHeatmapData;
  efficiency?: EfficiencyAnalysisData;
  network?: KnowledgeNetworkData;
  prediction?: PredictionData;
}

/**
 * 数据导出 Hook
 */
export function useDataExport(): UseDataExportReturn {
  const [isExporting, setIsExporting] = useState(false);
  const [progress, setProgress] = useState(0);

  // 转换为 CSV
  const convertToCSV = useCallback((data: unknown[]): string => {
    if (data.length === 0) return '';
    
    const headers = Object.keys(data[0] as Record<string, unknown>);
    const rows = data.map(item => {
      return headers.map(header => {
        const value = (item as Record<string, unknown>)[header];
        // 处理包含逗号或引号的值
        const stringValue = String(value ?? '');
        if (stringValue.includes(',') || stringValue.includes('"') || stringValue.includes('\n')) {
          return `"${stringValue.replace(/"/g, '""')}"`;
        }
        return stringValue;
      }).join(',');
    });
    
    return [headers.join(','), ...rows].join('\n');
  }, []);

  // 下载文件
  const downloadFile = useCallback((blob: Blob, filename: string) => {
    const url = window.URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = filename;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    window.URL.revokeObjectURL(url);
  }, []);

  // 导出为 CSV
  const exportToCSV = useCallback((data: unknown[], filename: string) => {
    const csv = convertToCSV(data);
    const blob = new Blob(['\ufeff' + csv], { type: 'text/csv;charset=utf-8;' });
    downloadFile(blob, `${filename}.csv`);
  }, [convertToCSV, downloadFile]);

  // 导出为 JSON
  const exportToJSON = useCallback((data: unknown, filename: string) => {
    const json = JSON.stringify(data, null, 2);
    const blob = new Blob([json], { type: 'application/json' });
    downloadFile(blob, `${filename}.json`);
  }, [downloadFile]);

  // 提取可导出的数据
  const extractExportData = useCallback((data: AnalyticsData, section: ExportSection): unknown => {
    const timestamp = new Date().toISOString().split('T')[0];
    
    switch (section) {
      case 'progress':
        return data.progress ? {
          metadata: { exportedAt: timestamp, section: '学习进度' },
          summary: data.progress.summary,
          trends: data.progress.trends,
          milestones: data.progress.milestones,
          goals: data.progress.goals,
        } : null;
        
      case 'heatmap':
        return data.heatmap ? {
          metadata: { exportedAt: timestamp, section: '概念掌握热力图' },
          categories: data.heatmap.categories,
          cells: data.heatmap.cells,
          overallStats: data.heatmap.overallStats,
        } : null;
        
      case 'efficiency':
        return data.efficiency ? {
          metadata: { exportedAt: timestamp, section: '学习效率分析' },
          overallEfficiency: data.efficiency.overallEfficiency,
          timeDistribution: data.efficiency.timeDistribution,
          learningPatterns: data.efficiency.learningPatterns,
          optimalConditions: data.efficiency.optimalConditions,
          recommendations: data.efficiency.recommendations,
        } : null;
        
      case 'network':
        return data.network ? {
          metadata: { exportedAt: timestamp, section: '知识网络分析' },
          nodes: data.network.nodes,
          edges: data.network.edges,
          networkStats: data.network.networkStats,
          communities: data.network.communities,
          bridges: data.network.bridges,
        } : null;
        
      case 'prediction':
        return data.prediction ? {
          metadata: { exportedAt: timestamp, section: '预测分析' },
          completionPrediction: data.prediction.completionPrediction,
          performanceForecast: data.prediction.performanceForecast,
          riskAnalysis: data.prediction.riskAnalysis,
          adaptiveSuggestions: data.prediction.adaptiveSuggestions,
        } : null;
        
      case 'all':
        return {
          metadata: { exportedAt: timestamp, section: '完整分析报告' },
          progress: data.progress,
          heatmap: data.heatmap,
          efficiency: data.efficiency,
          network: data.network,
          prediction: data.prediction,
        };
        
      default:
        return null;
    }
  }, []);

  // 生成 PDF（简化版本，实际项目中可以使用 jsPDF 或 puppeteer）
  const generatePDF = useCallback(async (data: AnalyticsData, section: ExportSection): Promise<Blob> => {
    // 这里使用一个简单的 HTML 转 PDF 的方法
    // 实际项目中可以使用 jsPDF、html2pdf.js 或后端生成
    const exportData = extractExportData(data, section);
    
    const htmlContent = `
      <!DOCTYPE html>
      <html>
      <head>
        <meta charset="UTF-8">
        <title>FormalMath 数据分析报告</title>
        <style>
          body { font-family: 'Microsoft YaHei', sans-serif; padding: 40px; }
          h1 { color: #2563eb; border-bottom: 2px solid #e5e7eb; padding-bottom: 10px; }
          h2 { color: #374151; margin-top: 30px; }
          table { width: 100%; border-collapse: collapse; margin: 20px 0; }
          th, td { border: 1px solid #e5e7eb; padding: 12px; text-align: left; }
          th { background-color: #f3f4f6; font-weight: 600; }
          .section { margin-bottom: 40px; }
          .footer { margin-top: 60px; padding-top: 20px; border-top: 1px solid #e5e7eb; font-size: 12px; color: #6b7280; }
        </style>
      </head>
      <body>
        <h1>FormalMath 数据分析报告</h1>
        <p>生成时间: ${new Date().toLocaleString('zh-CN')}</p>
        <pre>${JSON.stringify(exportData, null, 2)}</pre>
        <div class="footer">
          <p>本报告由 FormalMath 数据分析系统自动生成</p>
        </div>
      </body>
      </html>
    `;
    
    const blob = new Blob([htmlContent], { type: 'text/html' });
    return blob;
  }, [extractExportData]);

  // 导出数据
  const exportData = useCallback(async (
    data: AnalyticsData,
    options: ExportOptions
  ): Promise<ExportResult> => {
    setIsExporting(true);
    setProgress(0);
    
    try {
      const { format, section, filename, dateRange } = options;
      const defaultFilename = `formalmath-analytics-${section}-${new Date().toISOString().split('T')[0]}`;
      const finalFilename = filename || defaultFilename;
      
      setProgress(20);
      
      let blob: Blob;
      let resultFilename: string;
      
      switch (format) {
        case 'csv': {
          const exportData = extractExportData(data, section);
          const flatData = Array.isArray(exportData) ? exportData : [exportData];
          const csv = convertToCSV(flatData.filter(Boolean));
          blob = new Blob(['\ufeff' + csv], { type: 'text/csv;charset=utf-8;' });
          resultFilename = `${finalFilename}.csv`;
          break;
        }
        
        case 'json': {
          const exportData = extractExportData(data, section);
          const json = JSON.stringify(exportData, null, 2);
          blob = new Blob([json], { type: 'application/json' });
          resultFilename = `${finalFilename}.json`;
          break;
        }
        
        case 'pdf': {
          blob = await generatePDF(data, section);
          resultFilename = `${finalFilename}.html`; // 临时使用 HTML 格式
          break;
        }
        
        case 'excel': {
          // Excel 导出需要额外的库，这里使用 CSV 作为替代
          const exportData = extractExportData(data, section);
          const flatData = Array.isArray(exportData) ? exportData : [exportData];
          const csv = convertToCSV(flatData.filter(Boolean));
          blob = new Blob(['\ufeff' + csv], { type: 'application/vnd.ms-excel' });
          resultFilename = `${finalFilename}.xls`;
          break;
        }
        
        default:
          throw new Error(`不支持的导出格式: ${format}`);
      }
      
      setProgress(80);
      downloadFile(blob, resultFilename);
      setProgress(100);
      
      return {
        success: true,
        blob,
        filename: resultFilename,
      };
    } catch (err) {
      return {
        success: false,
        filename: '',
        error: err instanceof Error ? err.message : '导出失败',
      };
    } finally {
      setIsExporting(false);
      setProgress(0);
    }
  }, [convertToCSV, downloadFile, extractExportData, generatePDF]);

  return {
    isExporting,
    progress,
    exportData,
    exportToCSV,
    exportToJSON,
    downloadFile,
  };
}

export default useDataExport;

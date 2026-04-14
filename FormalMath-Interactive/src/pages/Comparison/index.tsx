// @ts-nocheck
import React, { useState } from 'react';
import { BarChart3, Table, LayoutGrid, Download } from 'lucide-react';
import { MatrixTable, ComparisonMatrix } from '@visualizations/MatrixTable';
import { cn } from '@utils/classNames';

// 模拟对比数据
const comparisonItems = [
  {
    id: '1',
    name: '欧几里得几何',
    description: '基于平行公设的几何体系',
    parallelPostulate: true,
    curvature: 0,
    triangleSum: 180,
    applications: ['建筑', '工程', '制图'],
  },
  {
    id: '2',
    name: '双曲几何',
    description: '否定平行公设的几何体系',
    parallelPostulate: false,
    curvature: -1,
    triangleSum: '< 180',
    applications: ['广义相对论', '宇宙学'],
  },
  {
    id: '3',
    name: '椭圆几何',
    description: '球面上的几何体系',
    parallelPostulate: false,
    curvature: 1,
    triangleSum: '> 180',
    applications: ['天文学', '导航'],
  },
];

const criteria = [
  { id: 'parallel', name: '平行公设', weight: 0.3 },
  { id: 'curvature', name: '曲率', weight: 0.3 },
  { id: 'triangle', name: '三角形内角和', weight: 0.2 },
  { id: 'apps', name: '应用领域', weight: 0.2 },
];

const matrixData = [
  [true, 0, '180°', '建筑、工程'],
  [false, -1, '< 180°', '相对论'],
  [false, 1, '> 180°', '天文学'],
];

export const Comparison: React.FC = () => {
  const [viewMode, setViewMode] = useState<'table' | 'matrix'>('table');

  const columns = [
    { key: 'name', header: '名称', sortable: true },
    { key: 'description', header: '描述', sortable: false },
    {
      key: 'parallelPostulate',
      header: '平行公设',
      render: (row: typeof comparisonItems[0]) => (
        <span className={cn(
          'px-2 py-1 rounded-full text-xs font-medium',
          row.parallelPostulate ? 'bg-green-100 text-green-700' : 'bg-red-100 text-red-700'
        )}>
          {row.parallelPostulate ? '成立' : '不成立'}
        </span>
      ),
    },
    { key: 'curvature', header: '曲率', format: (v: number) => v === 0 ? '0 (平坦)' : v },
    { key: 'triangleSum', header: '三角形内角和' },
    {
      key: 'applications',
      header: '应用领域',
      render: (row: typeof comparisonItems[0]) => (
        <div className="flex flex-wrap gap-1">
          {row.applications.map((app, i) => (
            <span key={i} className="px-2 py-0.5 bg-blue-50 text-blue-700 rounded text-xs">
              {app}
            </span>
          ))}
        </div>
      ),
    },
  ];

  return (
    <div className="flex-1 flex flex-col h-[calc(100vh-64px)]">
      {/* Header */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-gray-200 bg-white">
        <div className="flex items-center gap-3">
          <BarChart3 className="w-6 h-6 text-orange-600" />
          <div>
            <h1 className="text-xl font-semibold text-gray-900">对比分析</h1>
            <p className="text-sm text-gray-500">并排比较不同的数学理论和方法</p>
          </div>
        </div>
        
        <div className="flex items-center gap-3">
          <div className="flex items-center gap-2 bg-gray-100 p-1 rounded-lg">
            <button
              onClick={() => setViewMode('table')}
              className={cn(
                'flex items-center gap-1.5 px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
                viewMode === 'table' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600'
              )}
            >
              <Table className="w-4 h-4" />
              表格视图
            </button>
            <button
              onClick={() => setViewMode('matrix')}
              className={cn(
                'flex items-center gap-1.5 px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
                viewMode === 'matrix' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600'
              )}
            >
              <LayoutGrid className="w-4 h-4" />
              矩阵视图
            </button>
          </div>
          
          <button className="flex items-center gap-1.5 px-3 py-1.5 text-sm text-gray-600 bg-white border border-gray-300 rounded-lg hover:bg-gray-50">
            <Download className="w-4 h-4" />
            导出
          </button>
        </div>
      </div>

      {/* Content */}
      <div className="flex-1 overflow-auto p-6 bg-gray-50">
        {viewMode === 'table' ? (
          <MatrixTable
            data={comparisonItems}
            columns={columns}
            rowKey={row => row.id}
            className="max-w-5xl mx-auto"
          />
        ) : (
          <div className="max-w-4xl mx-auto">
            <div className="bg-white rounded-lg border border-gray-200 p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">属性对比矩阵</h3>
              <ComparisonMatrix
                rows={comparisonItems.map(i => i.name)}
                cols={criteria.map(c => c.name)}
                data={matrixData}
                highlightDiagonal={false}
              />
            </div>
            
            <div className="mt-6 bg-white rounded-lg border border-gray-200 p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">评估权重</h3>
              <div className="space-y-3">
                {criteria.map(c => (
                  <div key={c.id} className="flex items-center gap-4">
                    <span className="text-sm text-gray-600 w-32">{c.name}</span>
                    <div className="flex-1 h-2 bg-gray-200 rounded-full overflow-hidden">
                      <div
                        className="h-full bg-blue-500 rounded-full"
                        style={{ width: `${c.weight * 100}%` }}
                      />
                    </div>
                    <span className="text-sm font-medium text-gray-900 w-12">
                      {c.weight * 100}%
                    </span>
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default Comparison;

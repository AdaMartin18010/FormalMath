import React, { useState, useMemo } from 'react';
import { ArrowUpDown, ArrowUp, ArrowDown, Search, Download, Filter } from 'lucide-react';
import { cn } from '@utils/classNames';

type SortDirection = 'asc' | 'desc' | null;

interface Column<T> {
  key: string;
  header: string;
  width?: number;
  align?: 'left' | 'center' | 'right';
  sortable?: boolean;
  render?: (row: T) => React.ReactNode;
  format?: (value: unknown) => string;
}

interface MatrixTableProps<T> {
  data: T[];
  columns: Column<T>[];
  className?: string;
  searchable?: boolean;
  sortable?: boolean;
  pageable?: boolean;
  pageSize?: number;
  onRowClick?: (row: T) => void;
  selectedRows?: string[];
  rowKey: (row: T) => string;
  emptyMessage?: string;
}

export function MatrixTable<T>({
  data,
  columns,
  className,
  searchable = true,
  sortable = true,
  pageable = true,
  pageSize = 10,
  onRowClick,
  selectedRows = [],
  rowKey,
  emptyMessage = '暂无数据',
}: MatrixTableProps<T>) {
  const [searchQuery, setSearchQuery] = useState('');
  const [sortKey, setSortKey] = useState<string | null>(null);
  const [sortDirection, setSortDirection] = useState<SortDirection>(null);
  const [currentPage, setCurrentPage] = useState(1);

  // 过滤数据
  const filteredData = useMemo(() => {
    if (!searchQuery) return data;
    const query = searchQuery.toLowerCase();
    return data.filter(row => {
      return columns.some(col => {
        const value = (row as Record<string, unknown>)[col.key];
        if (value == null) return false;
        const formatted = col.format ? col.format(value) : String(value);
        return formatted.toLowerCase().includes(query);
      });
    });
  }, [data, searchQuery, columns]);

  // 排序数据
  const sortedData = useMemo(() => {
    if (!sortKey || !sortDirection) return filteredData;
    
    return [...filteredData].sort((a, b) => {
      const aVal = (a as Record<string, unknown>)[sortKey];
      const bVal = (b as Record<string, unknown>)[sortKey];
      
      if (aVal == null && bVal == null) return 0;
      if (aVal == null) return sortDirection === 'asc' ? -1 : 1;
      if (bVal == null) return sortDirection === 'asc' ? 1 : -1;
      
      if (typeof aVal === 'number' && typeof bVal === 'number') {
        return sortDirection === 'asc' ? aVal - bVal : bVal - aVal;
      }
      
      const aStr = String(aVal).toLowerCase();
      const bStr = String(bVal).toLowerCase();
      
      if (sortDirection === 'asc') {
        return aStr < bStr ? -1 : aStr > bStr ? 1 : 0;
      } else {
        return aStr > bStr ? -1 : aStr < bStr ? 1 : 0;
      }
    });
  }, [filteredData, sortKey, sortDirection]);

  // 分页数据
  const totalPages = Math.ceil(sortedData.length / pageSize);
  const paginatedData = useMemo(() => {
    if (!pageable) return sortedData;
    const start = (currentPage - 1) * pageSize;
    return sortedData.slice(start, start + pageSize);
  }, [sortedData, currentPage, pageSize, pageable]);

  // 处理排序
  const handleSort = (key: string) => {
    if (!sortable) return;
    
    if (sortKey === key) {
      setSortDirection(prev => {
        if (prev === 'asc') return 'desc';
        if (prev === 'desc') return null;
        return 'asc';
      });
      if (sortDirection === 'desc') {
        setSortKey(null);
      }
    } else {
      setSortKey(key);
      setSortDirection('asc');
    }
  };

  // 获取排序图标
  const getSortIcon = (key: string) => {
    if (sortKey !== key) return <ArrowUpDown className="w-4 h-4 text-gray-400" />;
    if (sortDirection === 'asc') return <ArrowUp className="w-4 h-4 text-blue-600" />;
    if (sortDirection === 'desc') return <ArrowDown className="w-4 h-4 text-blue-600" />;
    return <ArrowUpDown className="w-4 h-4 text-gray-400" />;
  };

  // 导出CSV
  const exportCSV = () => {
    const headers = columns.map(col => col.header).join(',');
    const rows = sortedData.map(row => {
      return columns.map(col => {
        const value = (row as Record<string, unknown>)[col.key];
        const formatted = col.format ? col.format(value) : String(value ?? '');
        return `"${formatted.replace(/"/g, '""')}"`;
      }).join(',');
    });
    
    const csv = [headers, ...rows].join('\n');
    const blob = new Blob([csv], { type: 'text/csv;charset=utf-8;' });
    const link = document.createElement('a');
    link.href = URL.createObjectURL(blob);
    link.download = `export-${Date.now()}.csv`;
    link.click();
  };

  return (
    <div className={cn('bg-white rounded-lg border border-gray-200 overflow-hidden', className)}>
      {/* Toolbar */}
      <div className="flex items-center justify-between gap-4 p-3 border-b border-gray-200 bg-gray-50">
        {searchable && (
          <div className="relative flex-1 max-w-xs">
            <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400" />
            <input
              type="text"
              placeholder="搜索..."
              value={searchQuery}
              onChange={(e) => {
                setSearchQuery(e.target.value);
                setCurrentPage(1);
              }}
              className="w-full pl-9 pr-3 py-1.5 text-sm border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500"
            />
          </div>
        )}
        
        <div className="flex items-center gap-2">
          <span className="text-sm text-gray-500">
            共 {filteredData.length} 条
          </span>
          <button
            onClick={exportCSV}
            className="flex items-center gap-1 px-3 py-1.5 text-sm text-gray-600 bg-white border border-gray-300 rounded-lg hover:bg-gray-50 transition-colors"
          >
            <Download className="w-4 h-4" />
            导出
          </button>
        </div>
      </div>

      {/* Table */}
      <div className="overflow-x-auto">
        <table className="w-full text-sm">
          <thead className="bg-gray-50 border-b border-gray-200">
            <tr>
              {columns.map(col => (
                <th
                  key={col.key}
                  className={cn(
                    'px-4 py-3 font-medium text-gray-700',
                    col.sortable && sortable && 'cursor-pointer hover:bg-gray-100',
                    col.align === 'center' && 'text-center',
                    col.align === 'right' && 'text-right'
                  )}
                  style={{ width: col.width }}
                  onClick={() => col.sortable && handleSort(col.key)}
                >
                  <div className={cn(
                    'flex items-center gap-1',
                    col.align === 'center' && 'justify-center',
                    col.align === 'right' && 'justify-end'
                  )}>
                    {col.header}
                    {col.sortable && sortable && getSortIcon(col.key)}
                  </div>
                </th>
              ))}
            </tr>
          </thead>
          <tbody className="divide-y divide-gray-100">
            {paginatedData.length === 0 ? (
              <tr>
                <td
                  colSpan={columns.length}
                  className="px-4 py-12 text-center text-gray-500"
                >
                  {emptyMessage}
                </td>
              </tr>
            ) : (
              paginatedData.map(row => {
                const key = rowKey(row);
                const isSelected = selectedRows.includes(key);
                
                return (
                  <tr
                    key={key}
                    onClick={() => onRowClick?.(row)}
                    className={cn(
                      'transition-colors',
                      onRowClick && 'cursor-pointer hover:bg-blue-50',
                      isSelected && 'bg-blue-50'
                    )}
                  >
                    {columns.map(col => {
                      const value = (row as Record<string, unknown>)[col.key];
                      
                      return (
                        <td
                          key={col.key}
                          className={cn(
                            'px-4 py-3 text-gray-900',
                            col.align === 'center' && 'text-center',
                            col.align === 'right' && 'text-right'
                          )}
                        >
                          {col.render ? (
                            col.render(row)
                          ) : col.format ? (
                            col.format(value)
                          ) : (
                            String(value ?? '-')
                          )}
                        </td>
                      );
                    })}
                  </tr>
                );
              })
            )}
          </tbody>
        </table>
      </div>

      {/* Pagination */}
      {pageable && totalPages > 1 && (
        <div className="flex items-center justify-between px-4 py-3 border-t border-gray-200 bg-gray-50">
          <div className="text-sm text-gray-500">
            显示 {(currentPage - 1) * pageSize + 1} - {Math.min(currentPage * pageSize, sortedData.length)} 条
          </div>
          <div className="flex items-center gap-1">
            <button
              onClick={() => setCurrentPage(1)}
              disabled={currentPage === 1}
              className="px-3 py-1 text-sm border border-gray-300 rounded-lg disabled:opacity-50 hover:bg-gray-100"
            >
              首页
            </button>
            <button
              onClick={() => setCurrentPage(p => Math.max(1, p - 1))}
              disabled={currentPage === 1}
              className="px-3 py-1 text-sm border border-gray-300 rounded-lg disabled:opacity-50 hover:bg-gray-100"
            >
              上一页
            </button>
            <span className="px-3 py-1 text-sm text-gray-600">
              {currentPage} / {totalPages}
            </span>
            <button
              onClick={() => setCurrentPage(p => Math.min(totalPages, p + 1))}
              disabled={currentPage === totalPages}
              className="px-3 py-1 text-sm border border-gray-300 rounded-lg disabled:opacity-50 hover:bg-gray-100"
            >
              下一页
            </button>
            <button
              onClick={() => setCurrentPage(totalPages)}
              disabled={currentPage === totalPages}
              className="px-3 py-1 text-sm border border-gray-300 rounded-lg disabled:opacity-50 hover:bg-gray-100"
            >
              末页
            </button>
          </div>
        </div>
      )}
    </div>
  );
}

/**
 * 对比矩阵组件
 */
interface ComparisonMatrixProps {
  rows: string[];
  cols: string[];
  data: (string | number | boolean | React.ReactNode)[][];
  highlightDiagonal?: boolean;
  className?: string;
}

export const ComparisonMatrix: React.FC<ComparisonMatrixProps> = ({
  rows,
  cols,
  data,
  highlightDiagonal = false,
  className,
}) => {
  return (
    <div className={cn('overflow-x-auto', className)}>
      <table className="w-full border-collapse">
        <thead>
          <tr>
            <th className="p-3 border border-gray-200 bg-gray-50 sticky left-0 z-10" />
            {cols.map((col, i) => (
              <th
                key={i}
                className="p-3 border border-gray-200 bg-gray-50 text-sm font-medium text-gray-700 min-w-[100px]"
              >
                {col}
              </th>
            ))}
          </tr>
        </thead>
        <tbody>
          {rows.map((row, rowIndex) => (
            <tr key={rowIndex}>
              <th className="p-3 border border-gray-200 bg-gray-50 text-sm font-medium text-gray-700 sticky left-0 z-10">
                {row}
              </th>
              {data[rowIndex]?.map((cell, colIndex) => {
                const isDiagonal = rowIndex === colIndex && highlightDiagonal;
                return (
                  <td
                    key={colIndex}
                    className={cn(
                      'p-3 border border-gray-200 text-center',
                      isDiagonal && 'bg-blue-50'
                    )}
                  >
                    {typeof cell === 'boolean' ? (
                      cell ? (
                        <span className="inline-flex items-center justify-center w-6 h-6 bg-green-100 text-green-600 rounded-full text-xs">✓</span>
                      ) : (
                        <span className="inline-flex items-center justify-center w-6 h-6 bg-red-100 text-red-600 rounded-full text-xs">✗</span>
                      )
                    ) : (
                      cell
                    )}
                  </td>
                );
              })}
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
};

export default MatrixTable;

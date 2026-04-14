// @ts-nocheck
import React, { useState } from 'react';
import { History, Play, Pause, SkipBack, SkipForward, Calendar } from 'lucide-react';
import { MermaidChart, mermaidTemplates } from '@visualizations/MermaidChart';
import { D3Graph } from '@visualizations/D3Graph';
import { cn } from '@utils/classNames';
import type { GraphData, EvolutionEvent, EvolutionSnapshot } from '@types';

// 模拟演化事件
const evolutionEvents: EvolutionEvent[] = [
  {
    id: '1',
    timestamp: -300,
    type: 'creation',
    description: '欧几里得《几何原本》出版',
    affectedNodes: ['euclid-geometry'],
    author: '欧几里得',
  },
  {
    id: '2',
    timestamp: 1637,
    type: 'creation',
    description: '笛卡尔创立解析几何',
    affectedNodes: ['analytic-geometry'],
    author: '笛卡尔',
  },
  {
    id: '3',
    timestamp: 1684,
    type: 'creation',
    description: '莱布尼茨发表微积分论文',
    affectedNodes: ['calculus'],
    author: '莱布尼茨',
  },
  {
    id: '4',
    timestamp: 1687,
    type: 'creation',
    description: '牛顿《自然哲学的数学原理》',
    affectedNodes: ['calculus', 'mechanics'],
    author: '牛顿',
  },
  {
    id: '5',
    timestamp: 1829,
    type: 'modification',
    description: '罗巴切夫斯基创立非欧几何',
    affectedNodes: ['non-euclidean-geometry'],
    author: '罗巴切夫斯基',
  },
  {
    id: '6',
    timestamp: 1854,
    type: 'creation',
    description: '黎曼提出黎曼几何',
    affectedNodes: ['riemann-geometry'],
    author: '黎曼',
  },
  {
    id: '7',
    timestamp: 1915,
    type: 'application',
    description: '广义相对论应用黎曼几何',
    affectedNodes: ['general-relativity'],
    author: '爱因斯坦',
  },
];

// 模拟快照数据
const snapshotData: GraphData = {
  nodes: [
    { id: '1', label: '几何', type: 'concept', status: 'verified' },
    { id: '2', label: '欧氏几何', type: 'concept', status: 'verified' },
    { id: '3', label: '非欧几何', type: 'concept', status: 'verified' },
    { id: '4', label: '解析几何', type: 'concept', status: 'verified' },
    { id: '5', label: '微分几何', type: 'concept', status: 'verified' },
    { id: '6', label: '欧几里得', type: 'mathematician', status: 'verified' },
    { id: '7', label: '笛卡尔', type: 'mathematician', status: 'verified' },
    { id: '8', label: '黎曼', type: 'mathematician', status: 'verified' },
  ],
  edges: [
    { id: 'e1', source: '2', target: '1', type: 'depends_on' },
    { id: 'e2', source: '3', target: '1', type: 'depends_on' },
    { id: 'e3', source: '4', target: '1', type: 'extends' },
    { id: 'e4', source: '5', target: '3', type: 'extends' },
    { id: 'e5', source: '6', target: '2', type: 'influences' },
    { id: 'e6', source: '7', target: '4', type: 'influences' },
    { id: 'e7', source: '8', target: '5', type: 'influences' },
  ],
};

const timelineData = mermaidTemplates.gantt(
  '几何学发展历程',
  [
    {
      name: '古代',
      tasks: [
        { name: '欧氏几何', start: '2024-01-01', duration: '10d' },
      ],
    },
    {
      name: '近代',
      tasks: [
        { name: '解析几何', start: '2024-01-11', duration: '5d' },
        { name: '微积分', start: '2024-01-16', duration: '5d' },
      ],
    },
    {
      name: '现代',
      tasks: [
        { name: '非欧几何', start: '2024-01-21', duration: '5d' },
        { name: '黎曼几何', start: '2024-01-26', duration: '5d' },
      ],
    },
  ]
);

export const Evolution: React.FC = () => {
  const [currentEventIndex, setCurrentEventIndex] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [viewMode, setViewMode] = useState<'timeline' | 'graph'>('timeline');

  const currentEvent = evolutionEvents[currentEventIndex];

  const handlePlay = () => {
    setIsPlaying(!isPlaying);
    if (!isPlaying && currentEventIndex < evolutionEvents.length - 1) {
      const interval = setInterval(() => {
        setCurrentEventIndex(prev => {
          if (prev >= evolutionEvents.length - 1) {
            setIsPlaying(false);
            clearInterval(interval);
            return prev;
          }
          return prev + 1;
        });
      }, 2000);
    }
  };

  const handlePrev = () => {
    setCurrentEventIndex(Math.max(0, currentEventIndex - 1));
  };

  const handleNext = () => {
    setCurrentEventIndex(Math.min(evolutionEvents.length - 1, currentEventIndex + 1));
  };

  const formatYear = (timestamp: number) => {
    if (timestamp < 0) {
      return `${Math.abs(timestamp)} BC`;
    }
    return `${timestamp} AD`;
  };

  return (
    <div className="flex-1 flex flex-col h-[calc(100vh-64px)]">
      {/* Header */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-gray-200 bg-white">
        <div className="flex items-center gap-3">
          <History className="w-6 h-6 text-indigo-600" />
          <div>
            <h1 className="text-xl font-semibold text-gray-900">演化历史</h1>
            <p className="text-sm text-gray-500">追溯数学理论的发展历程</p>
          </div>
        </div>
        
        <div className="flex items-center gap-2 bg-gray-100 p-1 rounded-lg">
          <button
            onClick={() => setViewMode('timeline')}
            className={cn(
              'px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
              viewMode === 'timeline' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600'
            )}
          >
            时间线
          </button>
          <button
            onClick={() => setViewMode('graph')}
            className={cn(
              'px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
              viewMode === 'graph' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600'
            )}
          >
            网络演化
          </button>
        </div>
      </div>

      {/* Content */}
      <div className="flex-1 flex flex-col">
        {viewMode === 'timeline' ? (
          <>
            {/* Timeline Visualization */}
            <div className="flex-1 p-6 bg-gray-50 overflow-auto">
              <MermaidChart
                definition={timelineData}
                className="max-w-4xl mx-auto"
              />
            </div>

            {/* Event Details & Controls */}
            <div className="border-t border-gray-200 bg-white">
              {/* Progress Bar */}
              <div className="px-6 py-2 border-b border-gray-200">
                <div className="flex items-center gap-4">
                  <span className="text-xs text-gray-500">
                    {currentEventIndex + 1} / {evolutionEvents.length}
                  </span>
                  <div className="flex-1 h-1 bg-gray-200 rounded-full overflow-hidden">
                    <div
                      className="h-full bg-blue-600 transition-all duration-300"
                      style={{ width: `${((currentEventIndex + 1) / evolutionEvents.length) * 100}%` }}
                    />
                  </div>
                </div>
              </div>

              {/* Current Event */}
              <div className="px-6 py-4">
                <div className="flex items-start gap-4">
                  <div className={cn(
                    'flex-shrink-0 w-12 h-12 rounded-full flex items-center justify-center',
                    currentEvent.type === 'creation' && 'bg-green-100',
                    currentEvent.type === 'modification' && 'bg-blue-100',
                    currentEvent.type === 'application' && 'bg-purple-100',
                  )}>
                    <Calendar className={cn(
                      'w-6 h-6',
                      currentEvent.type === 'creation' && 'text-green-600',
                      currentEvent.type === 'modification' && 'text-blue-600',
                      currentEvent.type === 'application' && 'text-purple-600',
                    )} />
                  </div>
                  <div className="flex-1">
                    <div className="flex items-center gap-2 mb-1">
                      <span className="text-lg font-semibold text-gray-900">
                        {formatYear(currentEvent.timestamp)}
                      </span>
                      <span className={cn(
                        'px-2 py-0.5 text-xs rounded-full',
                        currentEvent.type === 'creation' && 'bg-green-100 text-green-700',
                        currentEvent.type === 'modification' && 'bg-blue-100 text-blue-700',
                        currentEvent.type === 'application' && 'bg-purple-100 text-purple-700',
                      )}>
                        {currentEvent.type === 'creation' && '创建'}
                        {currentEvent.type === 'modification' && '修改'}
                        {currentEvent.type === 'application' && '应用'}
                      </span>
                    </div>
                    <p className="text-gray-700">{currentEvent.description}</p>
                    {currentEvent.author && (
                      <p className="text-sm text-gray-500 mt-1">
                        作者: {currentEvent.author}
                      </p>
                    )}
                  </div>
                </div>
              </div>

              {/* Controls */}
              <div className="flex items-center justify-center gap-4 px-6 py-4 border-t border-gray-200">
                <button
                  onClick={handlePrev}
                  disabled={currentEventIndex === 0}
                  className="p-2 text-gray-600 hover:bg-gray-100 rounded-lg disabled:opacity-50"
                >
                  <SkipBack className="w-5 h-5" />
                </button>
                <button
                  onClick={handlePlay}
                  className="flex items-center gap-2 px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
                >
                  {isPlaying ? <Pause className="w-5 h-5" /> : <Play className="w-5 h-5" />}
                  {isPlaying ? '暂停' : '播放'}
                </button>
                <button
                  onClick={handleNext}
                  disabled={currentEventIndex === evolutionEvents.length - 1}
                  className="p-2 text-gray-600 hover:bg-gray-100 rounded-lg disabled:opacity-50"
                >
                  <SkipForward className="w-5 h-5" />
                </button>
              </div>
            </div>
          </>
        ) : (
          <div className="flex-1 p-4">
            <D3Graph
              data={snapshotData}
              width={1000}
              height={600}
              config={{ showLabels: true, nodeSize: 30 }}
              className="w-full h-full"
            />
          </div>
        )}
      </div>
    </div>
  );
};

export default Evolution;

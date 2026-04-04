// ==================== 笔记知识图谱关联组件 ====================
import React, { useState, useCallback, useEffect, useRef } from 'react';
import { useNoteStore } from '../../stores/noteStore';
import {
  linkNoteToConcept,
  unlinkNoteFromConcept,
  suggestConceptLinks,
  fetchRelatedNotes,
} from '../../services/noteService';
import type { Note, NoteConceptLink } from '../../types/notes';
import {
  Network,
  Link2,
  Plus,
  X,
  Search,
  Lightbulb,
  BookOpen,
  ExternalLink,
  RefreshCw,
  MoreHorizontal,
  Check,
  AlertCircle,
} from 'lucide-react';

// 模拟知识图谱数据 - 实际项目中应该从API获取
const mockConcepts = [
  { id: 'c1', name: '群论', category: '代数学', description: '研究代数结构的数学分支' },
  { id: 'c2', name: '环', category: '代数学', description: '具有两个二元运算的代数结构' },
  { id: 'c3', name: '域', category: '代数学', description: '满足特定公理的交换环' },
  { id: 'c4', name: '向量空间', category: '线性代数', description: '向量的集合，满足特定运算规则' },
  { id: 'c5', name: '线性变换', category: '线性代数', description: '向量空间之间的映射' },
  { id: 'c6', name: '特征值', category: '线性代数', description: '线性变换的重要特征' },
  { id: 'c7', name: '微积分', category: '分析学', description: '研究变化和运动的数学' },
  { id: 'c8', name: '极限', category: '分析学', description: '微积分的基础概念' },
  { id: 'c9', name: '连续性', category: '分析学', description: '函数的重要性质' },
  { id: 'c10', name: '拓扑空间', category: '拓扑学', description: '研究空间性质的数学分支' },
];

interface NoteConceptGraphProps {
  note: Note;
  className?: string;
}

// 关系类型选项
const relationTypes = [
  { value: 'defines', label: '定义了', color: '#3B82F6' },
  { value: 'explains', label: '解释了', color: '#10B981' },
  { value: 'applies', label: '应用了', color: '#F59E0B' },
  { value: 'references', label: '引用了', color: '#8B5CF6' },
  { value: 'extends', label: '扩展了', color: '#EC4899' },
];

export const NoteConceptGraph: React.FC<NoteConceptGraphProps> = ({
  note,
  className = '',
}) => {
  const [linkedConcepts, setLinkedConcepts] = useState<NoteConceptLink[]>(
    note.aiAnalysis?.conceptLinks || []
  );
  const [suggestedLinks, setSuggestedLinks] = useState<NoteConceptLink[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [showAddModal, setShowAddModal] = useState(false);
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedConcept, setSelectedConcept] = useState<string | null>(null);
  const [selectedRelation, setSelectedRelation] = useState<string>('references');
  const [relatedNotes, setRelatedNotes] = useState<Note[]>([]);

  // 加载建议的关联
  const loadSuggestions = useCallback(async () => {
    setIsLoading(true);
    try {
      const response = await suggestConceptLinks(note.id);
      if (response.success && response.data) {
        // 过滤掉已关联的概念
        const existingIds = new Set(linkedConcepts.map((c) => c.conceptId));
        const filtered = response.data.filter((s) => !existingIds.has(s.conceptId));
        setSuggestedLinks(filtered);
      }
    } catch (error) {
      console.error('Failed to load suggestions:', error);
    } finally {
      setIsLoading(false);
    }
  }, [note.id, linkedConcepts]);

  // 加载相关笔记
  const loadRelatedNotes = useCallback(async () => {
    try {
      const response = await fetchRelatedNotes(note.id);
      if (response.success && response.data) {
        setRelatedNotes(response.data);
      }
    } catch (error) {
      console.error('Failed to load related notes:', error);
    }
  }, [note.id]);

  // 添加概念关联
  const handleAddLink = useCallback(async () => {
    if (!selectedConcept) return;

    try {
      await linkNoteToConcept(note.id, selectedConcept, selectedRelation as any);
      
      const concept = mockConcepts.find((c) => c.id === selectedConcept);
      if (concept) {
        const newLink: NoteConceptLink = {
          conceptId: selectedConcept,
          conceptName: concept.name,
          relationType: selectedRelation as any,
          relevanceScore: 1,
        };
        setLinkedConcepts((prev) => [...prev, newLink]);
      }
      
      setShowAddModal(false);
      setSelectedConcept(null);
      setSearchQuery('');
    } catch (error) {
      console.error('Failed to add link:', error);
    }
  }, [note.id, selectedConcept, selectedRelation]);

  // 移除概念关联
  const handleRemoveLink = useCallback(async (conceptId: string) => {
    try {
      await unlinkNoteFromConcept(note.id, conceptId);
      setLinkedConcepts((prev) => prev.filter((c) => c.conceptId !== conceptId));
    } catch (error) {
      console.error('Failed to remove link:', error);
    }
  }, [note.id]);

  // 接受AI建议
  const handleAcceptSuggestion = useCallback((suggestion: NoteConceptLink) => {
    setLinkedConcepts((prev) => [...prev, suggestion]);
    setSuggestedLinks((prev) => prev.filter((s) => s.conceptId !== suggestion.conceptId));
  }, []);

  // 过滤搜索结果
  const filteredConcepts = mockConcepts.filter(
    (c) =>
      !linkedConcepts.some((l) => l.conceptId === c.id) &&
      (c.name.toLowerCase().includes(searchQuery.toLowerCase()) ||
        c.category.toLowerCase().includes(searchQuery.toLowerCase()))
  );

  // 获取关系类型信息
  const getRelationInfo = (type: string) => {
    return relationTypes.find((r) => r.value === type) || relationTypes[3];
  };

  useEffect(() => {
    loadSuggestions();
    loadRelatedNotes();
  }, [loadSuggestions, loadRelatedNotes]);

  return (
    <div className={`bg-white rounded-xl shadow-sm border border-gray-200 ${className}`}>
      {/* 头部 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center">
          <Network className="w-5 h-5 text-blue-500 mr-2" />
          <h3 className="font-semibold text-gray-800">知识图谱关联</h3>
        </div>
        <div className="flex items-center space-x-2">
          <button
            onClick={loadSuggestions}
            disabled={isLoading}
            className="p-2 text-gray-400 hover:text-blue-500 rounded-lg hover:bg-blue-50 transition-colors"
            title="刷新建议"
          >
            <RefreshCw className={`w-4 h-4 ${isLoading ? 'animate-spin' : ''}`} />
          </button>
          <button
            onClick={() => setShowAddModal(true)}
            className="flex items-center px-3 py-1.5 bg-blue-500 text-white text-sm rounded-lg hover:bg-blue-600 transition-colors"
          >
            <Plus className="w-4 h-4 mr-1" />
            添加关联
          </button>
        </div>
      </div>

      <div className="p-4">
        {/* 已关联概念 */}
        <div className="mb-6">
          <h4 className="text-sm font-medium text-gray-700 mb-3 flex items-center">
            <Link2 className="w-4 h-4 mr-1" />
            已关联概念 ({linkedConcepts.length})
          </h4>
          {linkedConcepts.length === 0 ? (
            <div className="text-center py-6 bg-gray-50 rounded-lg">
              <Network className="w-8 h-8 text-gray-300 mx-auto mb-2" />
              <p className="text-sm text-gray-400">暂无关联概念</p>
              <p className="text-xs text-gray-400 mt-1">
                添加关联以建立知识连接
              </p>
            </div>
          ) : (
            <div className="space-y-2">
              {linkedConcepts.map((link) => {
                const relation = getRelationInfo(link.relationType);
                return (
                  <div
                    key={link.conceptId}
                    className="flex items-center justify-between p-3 bg-gray-50 rounded-lg group"
                  >
                    <div className="flex items-center">
                      <div
                        className="w-2 h-2 rounded-full mr-3"
                        style={{ backgroundColor: relation.color }}
                      />
                      <div>
                        <div className="flex items-center">
                          <span className="font-medium text-gray-800">
                            {link.conceptName}
                          </span>
                          <span
                            className="ml-2 px-2 py-0.5 text-xs rounded-full"
                            style={{
                              backgroundColor: relation.color + '20',
                              color: relation.color,
                            }}
                          >
                            {relation.label}
                          </span>
                        </div>
                        {link.relevanceScore > 0 && (
                          <div className="text-xs text-gray-400 mt-0.5">
                            相关度: {Math.round(link.relevanceScore * 100)}%
                          </div>
                        )}
                      </div>
                    </div>
                    <button
                      onClick={() => handleRemoveLink(link.conceptId)}
                      className="p-1.5 text-gray-400 hover:text-red-500 hover:bg-red-50 rounded-lg opacity-0 group-hover:opacity-100 transition-all"
                    >
                      <X className="w-4 h-4" />
                    </button>
                  </div>
                );
              })}
            </div>
          )}
        </div>

        {/* AI建议 */}
        {suggestedLinks.length > 0 && (
          <div className="mb-6">
            <h4 className="text-sm font-medium text-gray-700 mb-3 flex items-center">
              <Lightbulb className="w-4 h-4 mr-1 text-yellow-500" />
              AI 推荐关联 ({suggestedLinks.length})
            </h4>
            <div className="space-y-2">
              {suggestedLinks.slice(0, 5).map((suggestion) => {
                const relation = getRelationInfo(suggestion.relationType);
                return (
                  <div
                    key={suggestion.conceptId}
                    className="flex items-center justify-between p-3 bg-blue-50 border border-blue-100 rounded-lg"
                  >
                    <div className="flex items-center">
                      <div
                        className="w-2 h-2 rounded-full mr-3"
                        style={{ backgroundColor: relation.color }}
                      />
                      <div>
                        <div className="flex items-center">
                          <span className="font-medium text-gray-800">
                            {suggestion.conceptName}
                          </span>
                          <span
                            className="ml-2 px-2 py-0.5 text-xs rounded-full"
                            style={{
                              backgroundColor: relation.color + '20',
                              color: relation.color,
                            }}
                          >
                            {relation.label}
                          </span>
                        </div>
                        <div className="text-xs text-gray-500 mt-0.5">
                          相关度: {Math.round(suggestion.relevanceScore * 100)}%
                        </div>
                      </div>
                    </div>
                    <button
                      onClick={() => handleAcceptSuggestion(suggestion)}
                      className="p-1.5 text-blue-500 hover:bg-blue-100 rounded-lg transition-colors"
                    >
                      <Plus className="w-4 h-4" />
                    </button>
                  </div>
                );
              })}
            </div>
          </div>
        )}

        {/* 相关笔记 */}
        {relatedNotes.length > 0 && (
          <div>
            <h4 className="text-sm font-medium text-gray-700 mb-3 flex items-center">
              <BookOpen className="w-4 h-4 mr-1" />
              相关笔记 ({relatedNotes.length})
            </h4>
            <div className="space-y-2">
              {relatedNotes.slice(0, 5).map((relatedNote) => (
                <a
                  key={relatedNote.id}
                  href={`/notes/${relatedNote.id}`}
                  className="flex items-center justify-between p-3 bg-gray-50 rounded-lg hover:bg-gray-100 transition-colors"
                >
                  <div>
                    <span className="font-medium text-gray-800">
                      {relatedNote.title}
                    </span>
                    <div className="text-xs text-gray-400 mt-0.5">
                      {new Date(relatedNote.updatedAt).toLocaleDateString('zh-CN')}
                    </div>
                  </div>
                  <ExternalLink className="w-4 h-4 text-gray-400" />
                </a>
              ))}
            </div>
          </div>
        )}
      </div>

      {/* 添加关联弹窗 */}
      {showAddModal && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <div className="bg-white rounded-2xl p-6 w-[480px] max-w-full max-h-[80vh] flex flex-col">
            <div className="flex items-center justify-between mb-4">
              <h3 className="text-lg font-semibold text-gray-800">添加概念关联</h3>
              <button
                onClick={() => setShowAddModal(false)}
                className="p-1 text-gray-400 hover:text-gray-600"
              >
                <X className="w-5 h-5" />
              </button>
            </div>

            {/* 搜索 */}
            <div className="relative mb-4">
              <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400" />
              <input
                type="text"
                value={searchQuery}
                onChange={(e) => setSearchQuery(e.target.value)}
                placeholder="搜索概念..."
                className="w-full pl-10 pr-4 py-2 border border-gray-200 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
              />
            </div>

            {/* 概念列表 */}
            <div className="flex-1 overflow-y-auto mb-4 min-h-[200px]">
              {filteredConcepts.length === 0 ? (
                <div className="text-center py-8 text-gray-400">
                  <AlertCircle className="w-8 h-8 mx-auto mb-2 opacity-50" />
                  <p className="text-sm">未找到匹配的概念</p>
                </div>
              ) : (
                <div className="space-y-2">
                  {filteredConcepts.map((concept) => (
                    <button
                      key={concept.id}
                      onClick={() => setSelectedConcept(concept.id)}
                      className={`
                        w-full text-left p-3 rounded-lg border transition-all
                        ${selectedConcept === concept.id
                          ? 'border-blue-500 bg-blue-50'
                          : 'border-gray-200 hover:bg-gray-50'
                        }
                      `}
                    >
                      <div className="flex items-center justify-between">
                        <div>
                          <span className="font-medium text-gray-800">
                            {concept.name}
                          </span>
                          <span className="ml-2 text-xs text-gray-400">
                            {concept.category}
                          </span>
                        </div>
                        {selectedConcept === concept.id && (
                          <Check className="w-4 h-4 text-blue-500" />
                        )}
                      </div>
                      <p className="text-sm text-gray-500 mt-1">
                        {concept.description}
                      </p>
                    </button>
                  ))}
                </div>
              )}
            </div>

            {/* 关系类型选择 */}
            {selectedConcept && (
              <div className="mb-4">
                <label className="block text-sm font-medium text-gray-700 mb-2">
                  关联类型
                </label>
                <div className="flex flex-wrap gap-2">
                  {relationTypes.map((type) => (
                    <button
                      key={type.value}
                      onClick={() => setSelectedRelation(type.value)}
                      className={`
                        px-3 py-1.5 rounded-lg text-sm transition-all
                        ${selectedRelation === type.value
                          ? 'ring-2 ring-offset-1'
                          : 'border border-gray-200 hover:bg-gray-50'
                        }
                      `}
                      style={{
                        backgroundColor: selectedRelation === type.value ? type.color : type.color + '10',
                        color: selectedRelation === type.value ? 'white' : type.color,
                        '--tw-ring-color': type.color,
                      } as React.CSSProperties}
                    >
                      {type.label}
                    </button>
                  ))}
                </div>
              </div>
            )}

            {/* 操作按钮 */}
            <div className="flex justify-end space-x-2">
              <button
                onClick={() => setShowAddModal(false)}
                className="px-4 py-2 text-gray-600 hover:bg-gray-100 rounded-lg"
              >
                取消
              </button>
              <button
                onClick={handleAddLink}
                disabled={!selectedConcept}
                className="px-4 py-2 bg-blue-500 text-white rounded-lg hover:bg-blue-600 disabled:opacity-50"
              >
                添加关联
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default NoteConceptGraph;

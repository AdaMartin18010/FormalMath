import React from 'react';
import { LearningSuggestion } from '../../types';
import './SuggestionsList.css';

interface SuggestionsListProps {
  suggestions: LearningSuggestion[];
}

const SuggestionsList: React.FC<SuggestionsListProps> = ({ suggestions }) => {
  const getPriorityLabel = (priority: number): { text: string; className: string } => {
    switch (priority) {
      case 1:
        return { text: '最高', className: 'priority-highest' };
      case 2:
        return { text: '高', className: 'priority-high' };
      case 3:
        return { text: '中', className: 'priority-medium' };
      case 4:
        return { text: '低', className: 'priority-low' };
      default:
        return { text: '普通', className: 'priority-normal' };
    }
  };

  const getTypeIcon = (type: string): string => {
    switch (type) {
      case 'learning_path':
        return '📚';
      case 'learning_method':
        return '🎯';
      case 'practice':
        return '✏️';
      case 'weak_area':
        return '⚠️';
      default:
        return '💡';
    }
  };

  const getTypeLabel = (type: string): string => {
    switch (type) {
      case 'learning_path':
        return '学习路径';
      case 'learning_method':
        return '学习方法';
      case 'practice':
        return '练习建议';
      case 'weak_area':
        return '薄弱点强化';
      default:
        return '其他建议';
    }
  };

  return (
    <div className="suggestions-list">
      {suggestions.length === 0 ? (
        <div className="no-suggestions">
          <p>暂无学习建议</p>
        </div>
      ) : (
        suggestions.map((suggestion, index) => {
          const priority = getPriorityLabel(suggestion.priority);
          
          return (
            <div key={index} className="suggestion-card">
              <div className="suggestion-header">
                <div className="suggestion-type">
                  <span className="type-icon">{getTypeIcon(suggestion.type)}</span>
                  <span className="type-label">{getTypeLabel(suggestion.type)}</span>
                </div>
                <span className={`priority-badge ${priority.className}`}>
                  {priority.text}优先级
                </span>
              </div>
              
              <h4 className="suggestion-title">{suggestion.title}</h4>
              <p className="suggestion-content">{suggestion.content}</p>
              
              {suggestion.related_concepts.length > 0 && (
                <div className="related-concepts">
                  <span className="concepts-label">相关概念:</span>
                  <div className="concepts-tags">
                    {suggestion.related_concepts.map((concept, idx) => (
                      <span key={idx} className="concept-tag">
                        {concept}
                      </span>
                    ))}
                  </div>
                </div>
              )}
              
              {suggestion.recommended_resources && suggestion.recommended_resources.length > 0 && (
                <div className="recommended-resources">
                  <span className="resources-label">推荐资源:</span>
                  <ul className="resources-list">
                    {suggestion.recommended_resources.map((resource, idx) => (
                      <li key={idx} className="resource-item">
                        {resource.type}: {resource.content}
                      </li>
                    ))}
                  </ul>
                </div>
              )}
            </div>
          );
        })
      )}
    </div>
  );
};

export default SuggestionsList;

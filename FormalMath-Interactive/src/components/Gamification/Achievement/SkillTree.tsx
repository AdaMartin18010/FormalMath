/**
 * 技能树组件
 * 展示和交互技能树系统
 */

import React, { useState } from 'react';
import { Lock, Check, Zap, ChevronRight, Info } from 'lucide-react';
import type { SkillTree as SkillTreeType, SkillNode, SkillEffect } from '../../../types/gamification';

interface SkillTreeProps {
  skillTree: SkillTreeType;
  unlockedSkills: string[];
  userXP: number;
  onUnlockSkill: (skillId: string) => Promise<boolean>;
  onUpgradeSkill: (skillId: string) => Promise<boolean>;
}

const effectTypeLabels: Record<SkillEffect['type'], string> = {
  xp_boost: '经验加成',
  time_bonus: '时间奖励',
  hint_discount: '提示折扣',
  extra_lives: '额外生命',
  unlock_content: '解锁内容',
};

export const SkillTree: React.FC<SkillTreeProps> = ({
  skillTree,
  unlockedSkills,
  userXP,
  onUnlockSkill,
  onUpgradeSkill,
}) => {
  const [selectedSkill, setSelectedSkill] = useState<SkillNode | null>(null);
  const [isUnlocking, setIsUnlocking] = useState(false);

  const handleUnlock = async (skill: SkillNode) => {
    setIsUnlocking(true);
    const success = await onUnlockSkill(skill.id);
    if (success) {
      setSelectedSkill(null);
    }
    setIsUnlocking(false);
  };

  const handleUpgrade = async (skill: SkillNode) => {
    const success = await onUpgradeSkill(skill.id);
    if (success) {
      setSelectedSkill({ ...skill, currentLevel: skill.currentLevel + 1 });
    }
  };

  const isSkillAvailable = (skill: SkillNode): boolean => {
    return (
      !skill.isUnlocked &&
      skill.prerequisites.every((pre) => unlockedSkills.includes(pre))
    );
  };

  return (
    <div className="space-y-6">
      {/* 头部信息 */}
      <div className="bg-gradient-to-r from-indigo-600 to-purple-600 rounded-xl p-6 text-white">
        <h2 className="text-2xl font-bold mb-2">{skillTree.name}</h2>
        <p className="text-indigo-100">{skillTree.description}</p>
        <div className="mt-4 flex items-center gap-4">
          <div className="bg-white/20 px-4 py-2 rounded-lg">
            <span className="text-indigo-100">可用经验</span>
            <div className="text-2xl font-bold">{userXP.toLocaleString()} XP</div>
          </div>
          <div className="bg-white/20 px-4 py-2 rounded-lg">
            <span className="text-indigo-100">已解锁技能</span>
            <div className="text-2xl font-bold">{unlockedSkills.length}</div>
          </div>
        </div>
      </div>

      {/* 技能分支 */}
      <div className="space-y-8">
        {skillTree.branches.map((branch) => (
          <div key={branch.id} className="bg-white rounded-xl p-6 shadow-sm">
            <div className="flex items-center gap-3 mb-6">
              <div
                className="w-4 h-4 rounded-full"
                style={{ backgroundColor: branch.color }}
              />
              <h3 className="text-lg font-bold text-gray-900">{branch.name}</h3>
            </div>

            {/* 技能节点 */}
            <div className="flex flex-wrap gap-4">
              {branch.skills.map((skill, index) => {
                const isUnlocked = skill.isUnlocked;
                const isAvailable = isSkillAvailable(skill);
                const canUpgrade = isUnlocked && skill.currentLevel < skill.maxLevel;

                return (
                  <React.Fragment key={skill.id}>
                    {index > 0 && (
                      <div className="flex items-center">
                        <ChevronRight className="w-5 h-5 text-gray-300" />
                      </div>
                    )}
                    <button
                      onClick={() => setSelectedSkill(skill)}
                      className={`
                        relative w-24 h-24 rounded-xl border-2 transition-all duration-300
                        ${isUnlocked
                          ? 'bg-gradient-to-br from-green-400 to-green-500 border-green-600 text-white shadow-lg'
                          : isAvailable
                            ? 'bg-white border-blue-400 hover:border-blue-500 hover:shadow-md cursor-pointer'
                            : 'bg-gray-100 border-gray-300 text-gray-400 cursor-not-allowed'
                        }
                      `}
                    >
                      <div className="flex flex-col items-center justify-center h-full">
                        <span className="text-2xl mb-1">{skill.icon}</span>
                        <span className="text-xs font-medium line-clamp-1 px-1">
                          {skill.name}
                        </span>
                        {isUnlocked && (
                          <span className="text-xs mt-1">
                            Lv.{skill.currentLevel}/{skill.maxLevel}
                          </span>
                        )}
                      </div>

                      {/* 锁定图标 */}
                      {!isUnlocked && !isAvailable && (
                        <div className="absolute inset-0 flex items-center justify-center bg-gray-100/80 rounded-xl">
                          <Lock className="w-6 h-6 text-gray-400" />
                        </div>
                      )}

                      {/* 可解锁提示 */}
                      {isAvailable && (
                        <div className="absolute -top-2 -right-2 w-6 h-6 bg-blue-500 text-white rounded-full flex items-center justify-center animate-pulse">
                          <Zap className="w-3 h-3" />
                        </div>
                      )}
                    </button>
                  </React.Fragment>
                );
              })}
            </div>
          </div>
        ))}
      </div>

      {/* 技能详情弹窗 */}
      {selectedSkill && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50 p-4">
          <div className="bg-white rounded-2xl max-w-md w-full p-6">
            <div className="flex items-start justify-between mb-4">
              <div className="flex items-center gap-3">
                <div className="w-16 h-16 bg-gradient-to-br from-blue-400 to-purple-500 rounded-xl flex items-center justify-center text-3xl">
                  {selectedSkill.icon}
                </div>
                <div>
                  <h3 className="text-xl font-bold text-gray-900">{selectedSkill.name}</h3>
                  <p className="text-sm text-gray-500">
                    等级 {selectedSkill.currentLevel}/{selectedSkill.maxLevel}
                  </p>
                </div>
              </div>
              <button
                onClick={() => setSelectedSkill(null)}
                className="text-gray-400 hover:text-gray-600"
              >
                ✕
              </button>
            </div>

            <p className="text-gray-600 mb-6">{selectedSkill.description}</p>

            {/* 技能效果 */}
            <div className="space-y-3 mb-6">
              <h4 className="font-semibold text-gray-900 flex items-center gap-2">
                <Info className="w-4 h-4" />
                技能效果
              </h4>
              {selectedSkill.effects.map((effect, index) => (
                <div
                  key={index}
                  className="flex items-center justify-between p-3 bg-gray-50 rounded-lg"
                >
                  <span className="text-sm text-gray-600">
                    {effectTypeLabels[effect.type]}
                  </span>
                  <span className="font-medium text-green-600">
                    {effect.description}
                  </span>
                </div>
              ))}
            </div>

            {/* 解锁条件 */}
            {!selectedSkill.isUnlocked && (
              <div className="mb-6">
                <h4 className="font-semibold text-gray-900 mb-2">解锁条件</h4>
                {selectedSkill.prerequisites.length > 0 && (
                  <div className="text-sm text-gray-600 mb-2">
                    前置技能: {selectedSkill.prerequisites.join(', ')}
                  </div>
                )}
                <div className="text-sm text-gray-600">
                  需要: {selectedSkill.unlockCost.amount} {selectedSkill.unlockCost.type === 'xp' ? '经验' : '金币'}
                </div>
              </div>
            )}

            {/* 操作按钮 */}
            <div className="flex gap-3">
              <button
                onClick={() => setSelectedSkill(null)}
                className="flex-1 px-4 py-2 border rounded-lg hover:bg-gray-50"
              >
                关闭
              </button>
              
              {selectedSkill.isUnlocked ? (
                selectedSkill.currentLevel < selectedSkill.maxLevel && (
                  <button
                    onClick={() => handleUpgrade(selectedSkill)}
                    className="flex-1 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700"
                  >
                    升级技能
                  </button>
                )
              ) : (
                isSkillAvailable(selectedSkill) && (
                  <button
                    onClick={() => handleUnlock(selectedSkill)}
                    disabled={isUnlocking || userXP < selectedSkill.unlockCost.amount}
                    className={`
                      flex-1 px-4 py-2 rounded-lg text-white
                      ${userXP >= selectedSkill.unlockCost.amount
                        ? 'bg-green-600 hover:bg-green-700'
                        : 'bg-gray-400 cursor-not-allowed'
                      }
                    `}
                  >
                    {isUnlocking ? '解锁中...' : '解锁技能'}
                  </button>
                )
              )}
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default SkillTree;

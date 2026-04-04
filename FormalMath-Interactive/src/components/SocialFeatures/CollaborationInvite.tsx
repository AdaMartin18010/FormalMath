import React, { useState } from 'react';
import { 
  Users, 
  Link2, 
  Copy, 
  Check, 
  Mail, 
  MessageSquare,
  Share2,
  Clock,
  X
} from 'lucide-react';

interface CollaborationInviteProps {
  groupId: string;
  groupName: string;
  inviteLink: string;
  onClose?: () => void;
  onCopyLink?: () => void;
  onSendEmail?: (emails: string[]) => void;
  onGenerateLink?: (expiresIn: number) => void;
  className?: string;
}

interface InviteMethod {
  id: 'link' | 'email' | 'qr';
  name: string;
  icon: React.ReactNode;
  description: string;
}

export const CollaborationInvite: React.FC<CollaborationInviteProps> = ({
  groupId,
  groupName,
  inviteLink,
  onClose,
  onCopyLink,
  onSendEmail,
  onGenerateLink,
  className = '',
}) => {
  const [activeMethod, setActiveMethod] = useState<InviteMethod['id']>('link');
  const [copied, setCopied] = useState(false);
  const [emailInput, setEmailInput] = useState('');
  const [emailList, setEmailList] = useState<string[]>([]);
  const [expiryDays, setExpiryDays] = useState(7);
  const [maxUses, setMaxUses] = useState<number | null>(null);

  const inviteMethods: InviteMethod[] = [
    {
      id: 'link',
      name: '邀请链接',
      icon: <Link2 size={20} />,
      description: '生成分享链接，发送给任何人',
    },
    {
      id: 'email',
      name: '邮件邀请',
      icon: <Mail size={20} />,
      description: '发送邮件邀请给指定用户',
    },
    {
      id: 'qr',
      name: '二维码',
      icon: <Share2 size={20} />,
      description: '生成二维码，扫码加入',
    },
  ];

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(inviteLink);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
      onCopyLink?.();
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  };

  const handleAddEmail = () => {
    if (emailInput && !emailList.includes(emailInput)) {
      setEmailList([...emailList, emailInput]);
      setEmailInput('');
    }
  };

  const handleRemoveEmail = (email: string) => {
    setEmailList(emailList.filter(e => e !== email));
  };

  const handleSendInvites = () => {
    if (emailList.length > 0) {
      onSendEmail?.(emailList);
      setEmailList([]);
    }
  };

  const handleGenerateLink = () => {
    const expiresIn = expiryDays * 24 * 60 * 60 * 1000; // 转换为毫秒
    onGenerateLink?.(expiresIn);
  };

  const generateQRCode = () => {
    // 使用 Google Chart API 生成二维码
    return `https://chart.googleapis.com/chart?cht=qr&chs=300x300&chl=${encodeURIComponent(inviteLink)}`;
  };

  return (
    <div className={`bg-white rounded-lg shadow-xl max-w-lg w-full ${className}`}>
      {/* 头部 */}
      <div className="flex items-center justify-between p-4 border-b border-gray-200">
        <div className="flex items-center gap-3">
          <div className="w-10 h-10 bg-blue-100 rounded-lg flex items-center justify-center">
            <Users className="text-blue-500" size={20} />
          </div>
          <div>
            <h3 className="font-semibold text-gray-800">邀请成员</h3>
            <p className="text-sm text-gray-500">邀请他人加入「{groupName}」</p>
          </div>
        </div>
        <button
          onClick={onClose}
          className="p-2 text-gray-400 hover:text-gray-600 rounded-full hover:bg-gray-100"
        >
          <X size={20} />
        </button>
      </div>

      {/* 邀请方式选择 */}
      <div className="flex border-b border-gray-200">
        {inviteMethods.map((method) => (
          <button
            key={method.id}
            onClick={() => setActiveMethod(method.id)}
            className={`flex-1 py-3 px-4 text-sm font-medium transition-colors ${
              activeMethod === method.id
                ? 'text-blue-500 border-b-2 border-blue-500'
                : 'text-gray-500 hover:text-gray-700'
            }`}
          >
            <div className="flex items-center justify-center gap-2">
              {method.icon}
              {method.name}
            </div>
          </button>
        ))}
      </div>

      {/* 内容区 */}
      <div className="p-4">
        {activeMethod === 'link' && (
          <div className="space-y-4">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">
                邀请链接
              </label>
              <div className="flex gap-2">
                <input
                  type="text"
                  value={inviteLink}
                  readOnly
                  className="flex-1 px-4 py-2 bg-gray-50 border border-gray-200 rounded-lg text-sm text-gray-600"
                />
                <button
                  onClick={handleCopy}
                  className={`px-4 py-2 rounded-lg font-medium flex items-center gap-2 transition-colors ${
                    copied
                      ? 'bg-green-500 text-white'
                      : 'bg-blue-500 hover:bg-blue-600 text-white'
                  }`}
                >
                  {copied ? <Check size={18} /> : <Copy size={18} />}
                  {copied ? '已复制' : '复制'}
                </button>
              </div>
            </div>

            {/* 链接设置 */}
            <div className="space-y-3 pt-4 border-t border-gray-100">
              <h4 className="text-sm font-medium text-gray-700">链接设置</h4>
              
              <div>
                <label className="block text-sm text-gray-600 mb-1">
                  有效期: {expiryDays} 天
                </label>
                <input
                  type="range"
                  min="1"
                  max="30"
                  value={expiryDays}
                  onChange={(e) => setExpiryDays(parseInt(e.target.value))}
                  className="w-full"
                />
                <div className="flex justify-between text-xs text-gray-400 mt-1">
                  <span>1天</span>
                  <span>7天</span>
                  <span>30天</span>
                </div>
              </div>

              <div>
                <label className="block text-sm text-gray-600 mb-1">
                  最大使用次数
                </label>
                <select
                  value={maxUses || ''}
                  onChange={(e) => setMaxUses(e.target.value ? parseInt(e.target.value) : null)}
                  className="w-full px-3 py-2 border border-gray-200 rounded-lg text-sm"
                >
                  <option value="">无限制</option>
                  <option value="1">1 次</option>
                  <option value="5">5 次</option>
                  <option value="10">10 次</option>
                  <option value="50">50 次</option>
                  <option value="100">100 次</option>
                </select>
              </div>

              <button
                onClick={handleGenerateLink}
                className="w-full py-2 bg-gray-100 hover:bg-gray-200 text-gray-700 rounded-lg text-sm font-medium transition-colors"
              >
                生成新链接
              </button>
            </div>
          </div>
        )}

        {activeMethod === 'email' && (
          <div className="space-y-4">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">
                邮件地址
              </label>
              <div className="flex gap-2">
                <input
                  type="email"
                  value={emailInput}
                  onChange={(e) => setEmailInput(e.target.value)}
                  onKeyPress={(e) => e.key === 'Enter' && handleAddEmail()}
                  placeholder="输入邮箱地址，按回车添加"
                  className="flex-1 px-4 py-2 border border-gray-200 rounded-lg text-sm focus:outline-none focus:ring-2 focus:ring-blue-500"
                />
                <button
                  onClick={handleAddEmail}
                  className="px-4 py-2 bg-blue-500 hover:bg-blue-600 text-white rounded-lg transition-colors"
                >
                  添加
                </button>
              </div>
            </div>

            {/* 邮件列表 */}
            {emailList.length > 0 && (
              <div className="space-y-2">
                {emailList.map((email) => (
                  <div
                    key={email}
                    className="flex items-center justify-between p-2 bg-gray-50 rounded-lg"
                  >
                    <span className="text-sm text-gray-700">{email}</span>
                    <button
                      onClick={() => handleRemoveEmail(email)}
                      className="p-1 text-gray-400 hover:text-red-500 rounded"
                    >
                      <X size={16} />
                    </button>
                  </div>
                ))}
              </div>
            )}

            {/* 邀请信息模板 */}
            <div className="p-3 bg-gray-50 rounded-lg">
              <p className="text-sm text-gray-600 mb-2">邀请信息预览：</p>
              <div className="text-sm text-gray-700 space-y-1">
                <p className="font-medium">主题：邀请你加入学习组「{groupName}」</p>
                <p className="text-gray-500">
                  你好！我邀请你加入 FormalMath 的学习组「{groupName}」，一起学习进步！
                </p>
                <p className="text-blue-500">点击链接加入：{inviteLink}</p>
              </div>
            </div>

            <button
              onClick={handleSendInvites}
              disabled={emailList.length === 0}
              className="w-full py-3 bg-blue-500 hover:bg-blue-600 disabled:bg-gray-300 disabled:cursor-not-allowed text-white rounded-lg font-medium transition-colors"
            >
              发送邀请 ({emailList.length})
            </button>
          </div>
        )}

        {activeMethod === 'qr' && (
          <div className="text-center py-4">
            <div className="inline-block p-4 bg-white border-2 border-gray-200 rounded-xl">
              <img
                src={generateQRCode()}
                alt="邀请二维码"
                className="w-48 h-48"
              />
            </div>
            <p className="text-sm text-gray-500 mt-4">
              截图或保存二维码，分享给朋友扫码加入
            </p>
            <div className="flex justify-center gap-2 mt-4">
              <button
                onClick={() => {
                  const link = document.createElement('a');
                  link.href = generateQRCode();
                  link.download = `invite-${groupId}.png`;
                  link.click();
                }}
                className="px-4 py-2 bg-gray-100 hover:bg-gray-200 rounded-lg text-sm font-medium transition-colors"
              >
                保存二维码
              </button>
              <button
                onClick={handleCopy}
                className="px-4 py-2 bg-blue-500 hover:bg-blue-600 text-white rounded-lg text-sm font-medium transition-colors"
              >
                {copied ? '已复制' : '复制链接'}
              </button>
            </div>
          </div>
        )}
      </div>

      {/* 底部提示 */}
      <div className="px-4 py-3 bg-gray-50 rounded-b-lg flex items-center gap-2 text-sm text-gray-500">
        <Clock size={16} />
        <span>链接有效期 {expiryDays} 天，过期后需要重新生成</span>
      </div>
    </div>
  );
};

// 简单的邀请按钮组件
interface QuickInviteButtonProps {
  onClick?: () => void;
  memberCount?: number;
  maxMembers?: number;
  className?: string;
}

export const QuickInviteButton: React.FC<QuickInviteButtonProps> = ({
  onClick,
  memberCount = 0,
  maxMembers,
  className = '',
}) => {
  const isFull = maxMembers ? memberCount >= maxMembers : false;

  return (
    <button
      onClick={onClick}
      disabled={isFull}
      className={`
        flex items-center gap-2 px-4 py-2 rounded-lg font-medium transition-colors
        ${isFull 
          ? 'bg-gray-100 text-gray-400 cursor-not-allowed' 
          : 'bg-blue-500 hover:bg-blue-600 text-white'
        }
        ${className}
      `}
    >
      <UserPlus size={18} />
      <span>邀请成员</span>
      {maxMembers && (
        <span className="text-xs opacity-75">
          ({memberCount}/{maxMembers})
        </span>
      )}
    </button>
  );
};

// 受邀页面组件
interface InvitationAcceptProps {
  groupName: string;
  groupDescription?: string;
  groupAvatar?: string;
  inviterName: string;
  inviterAvatar?: string;
  memberCount: number;
  onAccept?: () => void;
  onDecline?: () => void;
  className?: string;
}

export const InvitationAccept: React.FC<InvitationAcceptProps> = ({
  groupName,
  groupDescription,
  groupAvatar,
  inviterName,
  inviterAvatar,
  memberCount,
  onAccept,
  onDecline,
  className = '',
}) => {
  return (
    <div className={`bg-white rounded-lg shadow-xl max-w-md w-full p-6 text-center ${className}`}>
      {/* 邀请者信息 */}
      <div className="mb-6">
        {inviterAvatar ? (
          <img
            src={inviterAvatar}
            alt={inviterName}
            className="w-16 h-16 rounded-full mx-auto mb-3 object-cover"
          />
        ) : (
          <div className="w-16 h-16 rounded-full bg-blue-100 mx-auto mb-3 flex items-center justify-center text-2xl text-blue-500">
            {inviterName[0]}
          </div>
        )}
        <p className="text-gray-600">
          <span className="font-medium text-gray-800">{inviterName}</span> 邀请你加入
        </p>
      </div>

      {/* 群组信息 */}
      <div className="mb-8">
        {groupAvatar ? (
          <img
            src={groupAvatar}
            alt={groupName}
            className="w-24 h-24 rounded-xl mx-auto mb-4 object-cover"
          />
        ) : (
          <div className="w-24 h-24 rounded-xl bg-gradient-to-br from-blue-500 to-purple-600 mx-auto mb-4 flex items-center justify-center text-white text-3xl font-bold">
            {groupName[0]}
          </div>
        )}
        <h2 className="text-2xl font-bold text-gray-800 mb-2">{groupName}</h2>
        {groupDescription && (
          <p className="text-gray-500 text-sm">{groupDescription}</p>
        )}
        <p className="text-sm text-gray-400 mt-2">
          <Users size={14} className="inline mr-1" />
          {memberCount} 位成员
        </p>
      </div>

      {/* 操作按钮 */}
      <div className="space-y-3">
        <button
          onClick={onAccept}
          className="w-full py-3 bg-blue-500 hover:bg-blue-600 text-white rounded-lg font-medium transition-colors"
        >
          接受邀请
        </button>
        <button
          onClick={onDecline}
          className="w-full py-3 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
        >
          拒绝
        </button>
      </div>
    </div>
  );
};

import { UserPlus } from 'lucide-react';

export default CollaborationInvite;

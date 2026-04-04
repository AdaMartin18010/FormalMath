// ==================== 笔记分享组件 ====================
import React, { useState, useCallback } from 'react';
import { shareNote, unshareNote, fetchSharedNote } from '../../services/noteService';
import type { Note, NoteShareSettings } from '../../types/notes';
import {
  Share2,
  Link2,
  Copy,
  Check,
  Lock,
  Globe,
  Eye,
  MessageSquare,
  Edit3,
  X,
  Calendar,
  ChevronDown,
  ChevronUp,
  Settings,
  Users,
  Mail,
  QrCode,
  Download,
} from 'lucide-react';

interface NoteShareProps {
  note: Note;
  onShare?: (settings: NoteShareSettings) => void;
  onUnshare?: () => void;
  className?: string;
}

export const NoteShare: React.FC<NoteShareProps> = ({
  note,
  onShare,
  onUnshare,
  className = '',
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const [isSharing, setIsSharing] = useState(false);
  const [copied, setCopied] = useState(false);
  const [showAdvanced, setShowAdvanced] = useState(false);
  const [shareSettings, setShareSettings] = useState<Partial<NoteShareSettings>>({
    isPublic: note.shareSettings?.isPublic ?? false,
    allowComments: note.shareSettings?.allowComments ?? true,
    allowEdit: note.shareSettings?.allowEdit ?? false,
    password: note.shareSettings?.password ?? '',
    expiresAt: note.shareSettings?.expiresAt ?? '',
  });

  // 生成分享链接
  const handleShare = useCallback(async () => {
    setIsSharing(true);
    try {
      const response = await shareNote(note.id, shareSettings);
      if (response.success && response.data) {
        onShare?.(response.data);
      }
    } catch (error) {
      console.error('Share failed:', error);
    } finally {
      setIsSharing(false);
    }
  }, [note.id, shareSettings, onShare]);

  // 取消分享
  const handleUnshare = useCallback(async () => {
    try {
      await unshareNote(note.id);
      onUnshare?.();
      setShareSettings({
        isPublic: false,
        allowComments: true,
        allowEdit: false,
        password: '',
        expiresAt: '',
      });
    } catch (error) {
      console.error('Unshare failed:', error);
    }
  }, [note.id, onUnshare]);

  // 复制链接
  const handleCopyLink = useCallback(() => {
    if (note.shareSettings?.shareLink) {
      navigator.clipboard.writeText(`${window.location.origin}/shared/${note.shareSettings.shareLink}`);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    }
  }, [note.shareSettings?.shareLink]);

  // 生成二维码
  const generateQRCode = useCallback(() => {
    // 这里应该调用QR码生成API
    console.log('Generate QR code for:', note.shareSettings?.shareLink);
  }, [note.shareSettings?.shareLink]);

  if (!isOpen) {
    return (
      <button
        onClick={() => setIsOpen(true)}
        className={`
          flex items-center px-4 py-2 rounded-lg
          ${note.shareSettings?.isPublic
            ? 'bg-green-100 text-green-700 hover:bg-green-200'
            : 'bg-gray-100 text-gray-700 hover:bg-gray-200'
          }
          transition-colors
          ${className}
        `}
      >
        <Share2 className="w-4 h-4 mr-2" />
        {note.shareSettings?.isPublic ? '已分享' : '分享'}
      </button>
    );
  }

  return (
    <div className={`bg-white rounded-xl shadow-lg border border-gray-200 ${className}`}>
      {/* 头部 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center">
          <Share2 className="w-5 h-5 text-blue-500 mr-2" />
          <h3 className="font-semibold text-gray-800">分享笔记</h3>
        </div>
        <button
          onClick={() => setIsOpen(false)}
          className="p-1 text-gray-400 hover:text-gray-600 rounded-lg hover:bg-gray-100"
        >
          <X className="w-5 h-5" />
        </button>
      </div>

      <div className="p-4 space-y-4">
        {/* 分享状态 */}
        {note.shareSettings?.isPublic ? (
          <div className="bg-green-50 border border-green-200 rounded-lg p-3">
            <div className="flex items-center text-green-700 mb-2">
              <Globe className="w-4 h-4 mr-2" />
              <span className="font-medium">笔记正在公开分享中</span>
            </div>
            <div className="flex items-center space-x-2">
              <input
                type="text"
                value={`${window.location.origin}/shared/${note.shareSettings.shareLink}`}
                readOnly
                className="flex-1 px-3 py-2 bg-white border border-green-200 rounded-lg text-sm text-gray-600"
              />
              <button
                onClick={handleCopyLink}
                className={`
                  px-3 py-2 rounded-lg text-sm font-medium
                  ${copied
                    ? 'bg-green-500 text-white'
                    : 'bg-green-100 text-green-700 hover:bg-green-200'
                  }
                `}
              >
                {copied ? (
                  <Check className="w-4 h-4" />
                ) : (
                  <Copy className="w-4 h-4" />
                )}
              </button>
            </div>
            <div className="flex items-center justify-between mt-3 text-sm">
              <span className="text-gray-500">
                {note.shareSettings.viewCount} 次查看
              </span>
              <button
                onClick={handleUnshare}
                className="text-red-600 hover:text-red-700"
              >
                取消分享
              </button>
            </div>
          </div>
        ) : (
          <div className="bg-gray-50 border border-gray-200 rounded-lg p-4">
            <div className="text-center">
              <div className="w-12 h-12 bg-gray-100 rounded-full flex items-center justify-center mx-auto mb-3">
                <Lock className="w-6 h-6 text-gray-400" />
              </div>
              <h4 className="font-medium text-gray-800 mb-1">笔记未分享</h4>
              <p className="text-sm text-gray-500 mb-4">
                开启分享后，其他人可以通过链接查看您的笔记
              </p>
              <button
                onClick={handleShare}
                disabled={isSharing}
                className="
                  px-6 py-2 bg-blue-500 text-white rounded-lg
                  hover:bg-blue-600 disabled:opacity-50
                  flex items-center mx-auto
                "
              >
                {isSharing ? (
                  <>
                    <div className="w-4 h-4 border-2 border-white border-t-transparent rounded-full animate-spin mr-2" />
                    生成链接中...
                  </>
                ) : (
                  <>
                    <Globe className="w-4 h-4 mr-2" />
                    开启分享
                  </>
                )}
              </button>
            </div>
          </div>
        )}

        {/* 分享统计 */}
        {note.shareSettings?.isPublic && (
          <div className="grid grid-cols-3 gap-3">
            <div className="bg-gray-50 rounded-lg p-3 text-center">
              <Eye className="w-5 h-5 text-gray-400 mx-auto mb-1" />
              <div className="text-lg font-semibold text-gray-800">
                {note.shareSettings.viewCount}
              </div>
              <div className="text-xs text-gray-500">查看次数</div>
            </div>
            <div className="bg-gray-50 rounded-lg p-3 text-center">
              <MessageSquare className="w-5 h-5 text-gray-400 mx-auto mb-1" />
              <div className="text-lg font-semibold text-gray-800">0</div>
              <div className="text-xs text-gray-500">评论</div>
            </div>
            <div className="bg-gray-50 rounded-lg p-3 text-center">
              <Users className="w-5 h-5 text-gray-400 mx-auto mb-1" />
              <div className="text-lg font-semibold text-gray-800">-</div>
              <div className="text-xs text-gray-500">访问者</div>
            </div>
          </div>
        )}

        {/* 高级设置 */}
        {note.shareSettings?.isPublic && (
          <div>
            <button
              onClick={() => setShowAdvanced(!showAdvanced)}
              className="flex items-center text-sm text-gray-600 hover:text-gray-800"
            >
              <Settings className="w-4 h-4 mr-2" />
              高级设置
              {showAdvanced ? (
                <ChevronUp className="w-4 h-4 ml-1" />
              ) : (
                <ChevronDown className="w-4 h-4 ml-1" />
              )}
            </button>

            {showAdvanced && (
              <div className="mt-3 space-y-3 bg-gray-50 rounded-lg p-4">
                {/* 权限设置 */}
                <div>
                  <label className="block text-sm font-medium text-gray-700 mb-2">
                    访问权限
                  </label>
                  <div className="space-y-2">
                    <label className="flex items-center">
                      <input
                        type="checkbox"
                        checked={shareSettings.allowComments}
                        onChange={(e) => {
                          const newSettings = { ...shareSettings, allowComments: e.target.checked };
                          setShareSettings(newSettings);
                          shareNote(note.id, newSettings);
                        }}
                        className="w-4 h-4 text-blue-500 rounded border-gray-300"
                      />
                      <span className="ml-2 text-sm text-gray-600">允许评论</span>
                    </label>
                    <label className="flex items-center">
                      <input
                        type="checkbox"
                        checked={shareSettings.allowEdit}
                        onChange={(e) => {
                          const newSettings = { ...shareSettings, allowEdit: e.target.checked };
                          setShareSettings(newSettings);
                          shareNote(note.id, newSettings);
                        }}
                        className="w-4 h-4 text-blue-500 rounded border-gray-300"
                      />
                      <span className="ml-2 text-sm text-gray-600">允许协作编辑</span>
                    </label>
                  </div>
                </div>

                {/* 密码保护 */}
                <div>
                  <label className="block text-sm font-medium text-gray-700 mb-2">
                    密码保护
                  </label>
                  <div className="flex items-center space-x-2">
                    <Lock className="w-4 h-4 text-gray-400" />
                    <input
                      type="text"
                      value={shareSettings.password}
                      onChange={(e) => setShareSettings({ ...shareSettings, password: e.target.value })}
                      placeholder="设置访问密码（可选）"
                      className="flex-1 px-3 py-2 border border-gray-200 rounded-lg text-sm"
                    />
                  </div>
                </div>

                {/* 过期时间 */}
                <div>
                  <label className="block text-sm font-medium text-gray-700 mb-2">
                    过期时间
                  </label>
                  <div className="flex items-center space-x-2">
                    <Calendar className="w-4 h-4 text-gray-400" />
                    <input
                      type="datetime-local"
                      value={shareSettings.expiresAt}
                      onChange={(e) => setShareSettings({ ...shareSettings, expiresAt: e.target.value })}
                      className="flex-1 px-3 py-2 border border-gray-200 rounded-lg text-sm"
                    />
                  </div>
                </div>

                {/* 保存设置 */}
                <button
                  onClick={handleShare}
                  disabled={isSharing}
                  className="
                    w-full py-2 bg-blue-500 text-white rounded-lg
                    hover:bg-blue-600 disabled:opacity-50
                    text-sm font-medium
                  "
                >
                  保存设置
                </button>
              </div>
            )}
          </div>
        )}

        {/* 其他分享方式 */}
        {note.shareSettings?.isPublic && (
          <div>
            <h4 className="text-sm font-medium text-gray-700 mb-3">其他分享方式</h4>
            <div className="grid grid-cols-4 gap-2">
              <button
                onClick={generateQRCode}
                className="flex flex-col items-center p-3 rounded-lg border border-gray-200 hover:bg-gray-50 transition-colors"
              >
                <QrCode className="w-5 h-5 text-gray-600 mb-1" />
                <span className="text-xs text-gray-600">二维码</span>
              </button>
              <button
                className="flex flex-col items-center p-3 rounded-lg border border-gray-200 hover:bg-gray-50 transition-colors"
              >
                <Mail className="w-5 h-5 text-gray-600 mb-1" />
                <span className="text-xs text-gray-600">邮件</span>
              </button>
              <button
                className="flex flex-col items-center p-3 rounded-lg border border-gray-200 hover:bg-gray-50 transition-colors"
              >
                <Download className="w-5 h-5 text-gray-600 mb-1" />
                <span className="text-xs text-gray-600">导出</span>
              </button>
              <button
                className="flex flex-col items-center p-3 rounded-lg border border-gray-200 hover:bg-gray-50 transition-colors"
              >
                <Link2 className="w-5 h-5 text-gray-600 mb-1" />
                <span className="text-xs text-gray-600">嵌入</span>
              </button>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default NoteShare;

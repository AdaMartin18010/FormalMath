import React, { useState, useCallback } from 'react';
import { 
  Share2, 
  Link2, 
  Check, 
  X,
  MessageCircle,
  Twitter,
  Facebook,
  Linkedin,
  Mail,
  Download,
  QrCode
} from 'lucide-react';

export type SharePlatform = 
  | 'wechat' 
  | 'weibo' 
  | 'twitter' 
  | 'facebook' 
  | 'linkedin' 
  | 'email' 
  | 'copy' 
  | 'qrcode';

interface ShareData {
  title: string;
  description: string;
  url: string;
  image?: string;
}

interface SocialShareProps {
  data: ShareData;
  platforms?: SharePlatform[];
  onShare?: (platform: SharePlatform) => void;
  onClose?: () => void;
  className?: string;
}

interface PlatformConfig {
  id: SharePlatform;
  name: string;
  icon: React.ReactNode;
  color: string;
  shareUrl?: (data: ShareData) => string;
}

const platformsConfig: PlatformConfig[] = [
  {
    id: 'wechat',
    name: '微信',
    icon: <MessageCircle size={24} />,
    color: '#07C160',
  },
  {
    id: 'weibo',
    name: '微博',
    icon: <Share2 size={24} />,
    color: '#E6162D',
    shareUrl: (data) => 
      `https://service.weibo.com/share/share.php?title=${encodeURIComponent(data.title + ' ' + data.description)}&url=${encodeURIComponent(data.url)}`,
  },
  {
    id: 'twitter',
    name: 'Twitter',
    icon: <Twitter size={24} />,
    color: '#1DA1F2',
    shareUrl: (data) => 
      `https://twitter.com/intent/tweet?text=${encodeURIComponent(data.title)}&url=${encodeURIComponent(data.url)}`,
  },
  {
    id: 'facebook',
    name: 'Facebook',
    icon: <Facebook size={24} />,
    color: '#4267B2',
    shareUrl: (data) => 
      `https://www.facebook.com/sharer/sharer.php?u=${encodeURIComponent(data.url)}`,
  },
  {
    id: 'linkedin',
    name: 'LinkedIn',
    icon: <Linkedin size={24} />,
    color: '#0077B5',
    shareUrl: (data) => 
      `https://www.linkedin.com/sharing/share-offsite/?url=${encodeURIComponent(data.url)}`,
  },
  {
    id: 'email',
    name: '邮件',
    icon: <Mail size={24} />,
    color: '#EA4335',
    shareUrl: (data) => 
      `mailto:?subject=${encodeURIComponent(data.title)}&body=${encodeURIComponent(data.description + '\n\n' + data.url)}`,
  },
];

export const SocialShare: React.FC<SocialShareProps> = ({
  data,
  platforms = ['wechat', 'weibo', 'twitter', 'copy', 'qrcode'],
  onShare,
  onClose,
  className = '',
}) => {
  const [copied, setCopied] = useState(false);
  const [showQRCode, setShowQRCode] = useState(false);
  const [activeTab, setActiveTab] = useState<'share' | 'embed'>('share');

  const availablePlatforms = platformsConfig.filter(p => platforms.includes(p.id));

  const handleShare = useCallback((platform: PlatformConfig) => {
    if (platform.shareUrl) {
      window.open(platform.shareUrl(data), '_blank', 'width=600,height=400');
    }
    onShare?.(platform.id);
  }, [data, onShare]);

  const handleCopyLink = useCallback(async () => {
    try {
      await navigator.clipboard.writeText(data.url);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
      onShare?.('copy');
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  }, [data.url, onShare]);

  const generateQRCode = () => {
    // 使用 Google Chart API 生成二维码
    const qrUrl = `https://chart.googleapis.com/chart?cht=qr&chs=300x300&chl=${encodeURIComponent(data.url)}`;
    return qrUrl;
  };

  const embedCode = `<iframe 
  src="${data.url}/embed" 
  width="100%" 
  height="600" 
  frameborder="0"
  title="${data.title}"
></iframe>`;

  const handleCopyEmbed = useCallback(async () => {
    try {
      await navigator.clipboard.writeText(embedCode);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  }, [embedCode]);

  return (
    <div className={`bg-white rounded-lg shadow-xl max-w-md w-full ${className}`}>
      {/* 头部 */}
      <div className="flex items-center justify-between p-4 border-b border-gray-200">
        <h3 className="text-lg font-semibold text-gray-800">分享</h3>
        <button
          onClick={onClose}
          className="p-1 text-gray-400 hover:text-gray-600 rounded-full hover:bg-gray-100"
        >
          <X size={20} />
        </button>
      </div>

      {/* 标签切换 */}
      <div className="flex border-b border-gray-200">
        <button
          onClick={() => setActiveTab('share')}
          className={`flex-1 py-3 text-sm font-medium transition-colors ${
            activeTab === 'share'
              ? 'text-blue-500 border-b-2 border-blue-500'
              : 'text-gray-500 hover:text-gray-700'
          }`}
        >
          分享到
        </button>
        <button
          onClick={() => setActiveTab('embed')}
          className={`flex-1 py-3 text-sm font-medium transition-colors ${
            activeTab === 'embed'
              ? 'text-blue-500 border-b-2 border-blue-500'
              : 'text-gray-500 hover:text-gray-700'
          }`}
        >
          嵌入代码
        </button>
      </div>

      {/* 内容区 */}
      <div className="p-4">
        {activeTab === 'share' ? (
          <>
            {/* 预览卡片 */}
            <div className="mb-4 p-3 bg-gray-50 rounded-lg">
              {data.image && (
                <img
                  src={data.image}
                  alt={data.title}
                  className="w-full h-32 object-cover rounded-lg mb-2"
                />
              )}
              <h4 className="font-medium text-gray-800 line-clamp-1">{data.title}</h4>
              <p className="text-sm text-gray-500 line-clamp-2 mt-1">{data.description}</p>
            </div>

            {/* 二维码弹窗 */}
            {showQRCode && (
              <div className="mb-4 p-4 bg-gray-50 rounded-lg text-center">
                <img
                  src={generateQRCode()}
                  alt="QR Code"
                  className="mx-auto w-48 h-48"
                />
                <p className="text-sm text-gray-500 mt-2">微信扫一扫分享</p>
                <button
                  onClick={() => setShowQRCode(false)}
                  className="mt-2 text-sm text-blue-500 hover:text-blue-600"
                >
                  关闭
                </button>
              </div>
            )}

            {/* 分享平台 */}
            <div className="grid grid-cols-4 gap-3">
              {availablePlatforms.map((platform) => (
                <button
                  key={platform.id}
                  onClick={() => handleShare(platform)}
                  className="flex flex-col items-center gap-2 p-3 rounded-lg hover:bg-gray-100 transition-colors"
                >
                  <div
                    className="w-12 h-12 rounded-full flex items-center justify-center text-white"
                    style={{ backgroundColor: platform.color }}
                  >
                    {platform.icon}
                  </div>
                  <span className="text-xs text-gray-600">{platform.name}</span>
                </button>
              ))}

              {/* 复制链接 */}
              {platforms.includes('copy') && (
                <button
                  onClick={handleCopyLink}
                  className="flex flex-col items-center gap-2 p-3 rounded-lg hover:bg-gray-100 transition-colors"
                >
                  <div className="w-12 h-12 rounded-full bg-gray-600 flex items-center justify-center text-white">
                    {copied ? <Check size={24} /> : <Link2 size={24} />}
                  </div>
                  <span className="text-xs text-gray-600">
                    {copied ? '已复制' : '复制链接'}
                  </span>
                </button>
              )}

              {/* 二维码 */}
              {platforms.includes('qrcode') && (
                <button
                  onClick={() => setShowQRCode(!showQRCode)}
                  className="flex flex-col items-center gap-2 p-3 rounded-lg hover:bg-gray-100 transition-colors"
                >
                  <div className="w-12 h-12 rounded-full bg-gray-600 flex items-center justify-center text-white">
                    <QrCode size={24} />
                  </div>
                  <span className="text-xs text-gray-600">二维码</span>
                </button>
              )}
            </div>
          </>
        ) : (
          /* 嵌入代码 */
          <div>
            <p className="text-sm text-gray-600 mb-3">
              将以下代码复制到你的网站或博客中：
            </p>
            <div className="relative">
              <pre className="p-3 bg-gray-900 text-gray-100 text-xs rounded-lg overflow-x-auto">
                {embedCode}
              </pre>
              <button
                onClick={handleCopyEmbed}
                className="absolute top-2 right-2 p-2 bg-white/10 hover:bg-white/20 rounded text-white"
              >
                {copied ? <Check size={16} /> : <Link2 size={16} />}
              </button>
            </div>
            <div className="mt-4 flex items-center gap-2 text-sm text-gray-500">
              <Download size={16} />
              <span>支持响应式布局</span>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

// 分享按钮组件
interface ShareButtonProps {
  data: ShareData;
  variant?: 'icon' | 'button' | 'outline';
  size?: 'sm' | 'md' | 'lg';
  className?: string;
  children?: React.ReactNode;
}

export const ShareButton: React.FC<ShareButtonProps> = ({
  data,
  variant = 'button',
  size = 'md',
  className = '',
  children,
}) => {
  const [isOpen, setIsOpen] = useState(false);

  const sizeClasses = {
    sm: variant === 'icon' ? 'w-8 h-8' : 'px-3 py-1.5 text-sm',
    md: variant === 'icon' ? 'w-10 h-10' : 'px-4 py-2',
    lg: variant === 'icon' ? 'w-12 h-12' : 'px-6 py-3 text-lg',
  };

  const variantClasses = {
    icon: 'bg-gray-100 hover:bg-gray-200 rounded-full flex items-center justify-center',
    button: 'bg-blue-500 hover:bg-blue-600 text-white rounded-lg flex items-center gap-2',
    outline: 'border-2 border-gray-300 hover:border-gray-400 text-gray-700 rounded-lg flex items-center gap-2',
  };

  // 使用原生分享 API
  const handleNativeShare = async () => {
    if (navigator.share) {
      try {
        await navigator.share({
          title: data.title,
          text: data.description,
          url: data.url,
        });
      } catch (err) {
        // 用户取消或分享失败，显示自定义分享弹窗
        setIsOpen(true);
      }
    } else {
      setIsOpen(true);
    }
  };

  return (
    <>
      <button
        onClick={handleNativeShare}
        className={`${sizeClasses[size]} ${variantClasses[variant]} transition-colors ${className}`}
      >
        <Share2 size={variant === 'icon' ? 18 : 20} />
        {variant !== 'icon' && (children || '分享')}
      </button>

      {/* 分享弹窗 */}
      {isOpen && (
        <div className="fixed inset-0 z-50 flex items-center justify-center p-4 bg-black/50">
          <SocialShare
            data={data}
            onClose={() => setIsOpen(false)}
          />
        </div>
      )}
    </>
  );
};

// 成就分享卡片
interface AchievementShareCardProps {
  achievement: {
    title: string;
    description: string;
    icon: string;
    earnedAt: string;
  };
  user: {
    name: string;
    avatar?: string;
  };
  stats: {
    studyDays: number;
    problemsSolved: number;
  };
  className?: string;
}

export const AchievementShareCard: React.FC<AchievementShareCardProps> = ({
  achievement,
  user,
  stats,
  className = '',
}) => {
  return (
    <div className={`bg-gradient-to-br from-blue-500 to-purple-600 rounded-xl p-6 text-white ${className}`}>
      <div className="flex items-center gap-3 mb-4">
        {user.avatar ? (
          <img src={user.avatar} alt={user.name} className="w-12 h-12 rounded-full" />
        ) : (
          <div className="w-12 h-12 rounded-full bg-white/20 flex items-center justify-center text-xl">
            {user.name[0]}
          </div>
        )}
        <div>
          <p className="font-medium">{user.name}</p>
          <p className="text-sm text-white/70">获得了新成就</p>
        </div>
      </div>

      <div className="text-center py-6">
        <div className="text-6xl mb-4">{achievement.icon}</div>
        <h3 className="text-2xl font-bold mb-2">{achievement.title}</h3>
        <p className="text-white/80">{achievement.description}</p>
      </div>

      <div className="flex justify-center gap-8 mt-6 pt-6 border-t border-white/20">
        <div className="text-center">
          <p className="text-2xl font-bold">{stats.studyDays}</p>
          <p className="text-sm text-white/70">学习天数</p>
        </div>
        <div className="text-center">
          <p className="text-2xl font-bold">{stats.problemsSolved}</p>
          <p className="text-sm text-white/70">解题数量</p>
        </div>
      </div>

      <div className="mt-6 text-center text-sm text-white/60">
        {achievement.earnedAt}
      </div>
    </div>
  );
};

export default SocialShare;

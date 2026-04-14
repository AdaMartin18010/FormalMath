// @ts-nocheck
import React, { useState, useCallback } from 'react';
import { 
  Share2, 
  Twitter, 
  Facebook, 
  Linkedin,
  Link2,
  Check,
  MessageCircle,
  Send,
  Bookmark,
  BookmarkCheck,
  ThumbsUp,
  Eye
} from 'lucide-react';

export type ShareButtonPlatform = 
  | 'twitter' 
  | 'facebook' 
  | 'linkedin' 
  | 'weibo'
  | 'wechat'
  | 'telegram'
  | 'whatsapp'
  | 'reddit'
  | 'pinterest'
  | 'copy';

export interface ShareCount {
  platform: ShareButtonPlatform;
  count: number;
}

export interface ShareButtonsProps {
  url: string;
  title: string;
  description?: string;
  image?: string;
  hashtags?: string[];
  via?: string;
  counts?: ShareCount[];
  platforms?: ShareButtonPlatform[];
  onShare?: (platform: ShareButtonPlatform) => void;
  className?: string;
  variant?: 'default' | 'minimal' | 'pill';
  size?: 'sm' | 'md' | 'lg';
  showCount?: boolean;
}

interface PlatformConfig {
  id: ShareButtonPlatform;
  name: string;
  icon: React.ReactNode;
  color: string;
  hoverColor: string;
  shareUrl: (data: { url: string; title: string; description: string; hashtags: string[]; via?: string }) => string;
}

const platformsConfig: PlatformConfig[] = [
  {
    id: 'twitter',
    name: 'Twitter',
    icon: <Twitter size={18} />,
    color: 'bg-[#1DA1F2]',
    hoverColor: 'hover:bg-[#1a91da]',
    shareUrl: ({ url, title, hashtags, via }) => 
      `https://twitter.com/intent/tweet?url=${encodeURIComponent(url)}&text=${encodeURIComponent(title)}&hashtags=${hashtags.join(',')}${via ? `&via=${via}` : ''}`,
  },
  {
    id: 'facebook',
    name: 'Facebook',
    icon: <Facebook size={18} />,
    color: 'bg-[#4267B2]',
    hoverColor: 'hover:bg-[#365899]',
    shareUrl: ({ url }) => 
      `https://www.facebook.com/sharer/sharer.php?u=${encodeURIComponent(url)}`,
  },
  {
    id: 'linkedin',
    name: 'LinkedIn',
    icon: <Linkedin size={18} />,
    color: 'bg-[#0077B5]',
    hoverColor: 'hover:bg-[#006399]',
    shareUrl: ({ url, title }) => 
      `https://www.linkedin.com/sharing/share-offsite/?url=${encodeURIComponent(url)}&title=${encodeURIComponent(title)}`,
  },
  {
    id: 'weibo',
    name: '微博',
    icon: <Share2 size={18} />,
    color: 'bg-[#E6162D]',
    hoverColor: 'hover:bg-[#c91327]',
    shareUrl: ({ url, title, image }) => 
      `https://service.weibo.com/share/share.php?url=${encodeURIComponent(url)}&title=${encodeURIComponent(title)}${image ? `&pic=${encodeURIComponent(image)}` : ''}`,
  },
  {
    id: 'telegram',
    name: 'Telegram',
    icon: <Send size={18} />,
    color: 'bg-[#0088cc]',
    hoverColor: 'hover:bg-[#0077b3]',
    shareUrl: ({ url, title }) => 
      `https://t.me/share/url?url=${encodeURIComponent(url)}&text=${encodeURIComponent(title)}`,
  },
  {
    id: 'whatsapp',
    name: 'WhatsApp',
    icon: <MessageCircle size={18} />,
    color: 'bg-[#25D366]',
    hoverColor: 'hover:bg-[#1ebe57]',
    shareUrl: ({ url, title }) => 
      `https://wa.me/?text=${encodeURIComponent(title + ' ' + url)}`,
  },
  {
    id: 'reddit',
    name: 'Reddit',
    icon: <Share2 size={18} />,
    color: 'bg-[#FF4500]',
    hoverColor: 'hover:bg-[#e03e00]',
    shareUrl: ({ url, title }) => 
      `https://www.reddit.com/submit?url=${encodeURIComponent(url)}&title=${encodeURIComponent(title)}`,
  },
  {
    id: 'pinterest',
    name: 'Pinterest',
    icon: <Share2 size={18} />,
    color: 'bg-[#E60023]',
    hoverColor: 'hover:bg-[#cc0020]',
    shareUrl: ({ url, title, image }) => 
      `https://pinterest.com/pin/create/button/?url=${encodeURIComponent(url)}&description=${encodeURIComponent(title)}${image ? `&media=${encodeURIComponent(image)}` : ''}`,
  },
];

const sizeClasses = {
  sm: { button: 'w-8 h-8', icon: 14 },
  md: { button: 'w-10 h-10', icon: 18 },
  lg: { button: 'w-12 h-12', icon: 20 },
};

const variantClasses = {
  default: 'rounded-lg',
  minimal: 'rounded hover:bg-gray-100',
  pill: 'rounded-full',
};

export const ShareButtons: React.FC<ShareButtonsProps> = ({
  url,
  title,
  description = '',
  image = '',
  hashtags = [],
  via,
  counts = [],
  platforms = ['twitter', 'facebook', 'linkedin', 'copy'],
  onShare,
  className = '',
  variant = 'default',
  size = 'md',
  showCount = false,
}) => {
  const [copied, setCopied] = useState(false);
  const [activePlatform, setActivePlatform] = useState<ShareButtonPlatform | null>(null);

  const availablePlatforms = platformsConfig.filter(p => platforms.includes(p.id));

  const handleShare = useCallback((platform: PlatformConfig) => {
    setActivePlatform(platform.id);
    
    const shareWindow = window.open(
      platform.shareUrl({ url, title, description, hashtags, via }),
      `${platform.name}Share`,
      'width=600,height=400,scrollbars=yes'
    );

    if (shareWindow) {
      const checkWindow = setInterval(() => {
        if (shareWindow.closed) {
          clearInterval(checkWindow);
          setActivePlatform(null);
        }
      }, 1000);
    }

    onShare?.(platform.id);
  }, [url, title, description, hashtags, via, onShare]);

  const handleCopy = useCallback(async () => {
    try {
      await navigator.clipboard.writeText(url);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
      onShare?.('copy');
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  }, [url, onShare]);

  const getCount = (platformId: ShareButtonPlatform): number => {
    return counts.find(c => c.platform === platformId)?.count || 0;
  };

  return (
    <div className={`flex items-center gap-2 ${className}`}>
      {availablePlatforms.map((platform) => {
        const count = getCount(platform.id);
        const Icon = React.cloneElement(platform.icon as React.ReactElement, {
          size: sizeClasses[size].icon,
        });

        return (
          <div key={platform.id} className="relative">
            <button
              onClick={() => handleShare(platform)}
              disabled={activePlatform === platform.id}
              className={`
                flex items-center justify-center
                ${sizeClasses[size].button}
                ${platform.color}
                ${platform.hoverColor}
                ${variantClasses[variant]}
                text-white transition-all duration-200
                ${activePlatform === platform.id ? 'opacity-75' : ''}
                ${variant === 'minimal' ? '!bg-transparent !hover:bg-gray-100 !text-gray-600' : ''}
              `}
              title={platform.name}
            >
              {activePlatform === platform.id ? (
                <div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />
              ) : (
                Icon
              )}
            </button>
            {showCount && count > 0 && (
              <span className="absolute -top-2 -right-2 min-w-[18px] h-[18px] px-1 bg-gray-800 text-white text-xs rounded-full flex items-center justify-center">
                {count > 999 ? '999+' : count}
              </span>
            )}
          </div>
        );
      })}

      {/* Copy Link Button */}
      {platforms.includes('copy') && (
        <button
          onClick={handleCopy}
          className={`
            flex items-center justify-center
            ${sizeClasses[size].button}
            bg-gray-100 hover:bg-gray-200 text-gray-600
            ${variantClasses[variant]}
            transition-all duration-200
          `}
          title={copied ? '已复制' : '复制链接'}
        >
          {copied ? <Check size={sizeClasses[size].icon} className="text-green-600" /> : <Link2 size={sizeClasses[size].icon} />}
        </button>
      )}
    </div>
  );
};

// 浮动分享按钮
export interface FloatingShareButtonProps {
  url: string;
  title: string;
  description?: string;
  image?: string;
  hashtags?: string[];
  onShare?: (platform: ShareButtonPlatform) => void;
  className?: string;
  position?: 'bottom-right' | 'bottom-left' | 'top-right' | 'top-left';
  offset?: { x: number; y: number };
}

export const FloatingShareButton: React.FC<FloatingShareButtonProps> = ({
  url,
  title,
  description,
  image,
  hashtags,
  onShare,
  className = '',
  position = 'bottom-right',
  offset = { x: 24, y: 24 },
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const [showTooltip, setShowTooltip] = useState(false);

  const positionClasses = {
    'bottom-right': `bottom-${offset.y} right-${offset.x}`,
    'bottom-left': `bottom-${offset.y} left-${offset.x}`,
    'top-right': `top-${offset.y} right-${offset.x}`,
    'top-left': `top-${offset.y} left-${offset.x}`,
  };

  const handleShare = (platform: ShareButtonPlatform) => {
    onShare?.(platform);
    setIsOpen(false);
  };

  // Native share
  const handleNativeShare = async () => {
    if (navigator.share) {
      try {
        await navigator.share({
          title,
          text: description,
          url,
        });
      } catch (err) {
        // User cancelled
      }
    } else {
      setIsOpen(!isOpen);
    }
  };

  return (
    <div className={`fixed ${positionClasses[position]} z-50 ${className}`} style={{ bottom: offset.y, right: offset.x }}>
      {/* Share Menu */}
      {isOpen && (
        <div className="absolute bottom-full right-0 mb-2 p-3 bg-white rounded-xl shadow-xl border border-gray-100 animate-in fade-in slide-in-from-bottom-2">
          <ShareButtons
            url={url}
            title={title}
            description={description}
            image={image}
            hashtags={hashtags}
            onShare={handleShare}
            variant="pill"
            size="md"
            className="flex-col"
          />
        </div>
      )}

      {/* Main Button */}
      <button
        onClick={handleNativeShare}
        onMouseEnter={() => setShowTooltip(true)}
        onMouseLeave={() => setShowTooltip(false)}
        className={`
          w-14 h-14 rounded-full flex items-center justify-center
          bg-blue-500 hover:bg-blue-600 text-white
          shadow-lg hover:shadow-xl
          transition-all duration-200
          ${isOpen ? 'rotate-45' : ''}
        `}
      >
        <Share2 size={24} />
      </button>

      {/* Tooltip */}
      {showTooltip && !isOpen && (
        <div className="absolute bottom-full right-0 mb-2 px-3 py-1.5 bg-gray-800 text-white text-sm rounded-lg whitespace-nowrap">
          分享内容
          <div className="absolute top-full right-6 -translate-x-1/2 border-4 border-transparent border-t-gray-800" />
        </div>
      )}
    </div>
  );
};

// 内联分享按钮组（带统计）
export interface InlineShareButtonsProps {
  url: string;
  title: string;
  likes?: number;
  views?: number;
  bookmarks?: number;
  isLiked?: boolean;
  isBookmarked?: boolean;
  onLike?: () => void;
  onBookmark?: () => void;
  onShare?: (platform: ShareButtonPlatform) => void;
  className?: string;
}

export const InlineShareButtons: React.FC<InlineShareButtonsProps> = ({
  url,
  title,
  likes = 0,
  views = 0,
  bookmarks = 0,
  isLiked = false,
  isBookmarked = false,
  onLike,
  onBookmark,
  onShare,
  className = '',
}) => {
  const [showShareMenu, setShowShareMenu] = useState(false);

  const formatNumber = (num: number): string => {
    if (num >= 1000000) return (num / 1000000).toFixed(1) + 'M';
    if (num >= 1000) return (num / 1000).toFixed(1) + 'K';
    return num.toString();
  };

  return (
    <div className={`flex items-center gap-4 ${className}`}>
      {/* Stats */}
      <div className="flex items-center gap-4 text-sm text-gray-500">
        {views > 0 && (
          <div className="flex items-center gap-1">
            <Eye size={16} />
            <span>{formatNumber(views)}</span>
          </div>
        )}
      </div>

      <div className="flex-1" />

      {/* Actions */}
      <div className="flex items-center gap-2">
        {/* Like */}
        <button
          onClick={onLike}
          className={`
            flex items-center gap-2 px-3 py-1.5 rounded-lg transition-colors
            ${isLiked 
              ? 'bg-red-50 text-red-600' 
              : 'hover:bg-gray-100 text-gray-600'
            }
          `}
        >
          <ThumbsUp size={18} className={isLiked ? 'fill-current' : ''} />
          <span className="text-sm font-medium">{formatNumber(likes)}</span>
        </button>

        {/* Bookmark */}
        <button
          onClick={onBookmark}
          className={`
            p-2 rounded-lg transition-colors
            ${isBookmarked 
              ? 'bg-blue-50 text-blue-600' 
              : 'hover:bg-gray-100 text-gray-600'
            }
          `}
          title={isBookmarked ? '已收藏' : '收藏'}
        >
          {isBookmarked ? <BookmarkCheck size={18} /> : <Bookmark size={18} />}
        </button>

        {/* Share */}
        <div className="relative">
          <button
            onClick={() => setShowShareMenu(!showShareMenu)}
            className="flex items-center gap-2 px-3 py-1.5 rounded-lg hover:bg-gray-100 text-gray-600 transition-colors"
          >
            <Share2 size={18} />
            <span className="text-sm font-medium">分享</span>
          </button>

          {/* Share Dropdown */}
          {showShareMenu && (
            <>
              <div 
                className="fixed inset-0 z-40"
                onClick={() => setShowShareMenu(false)}
              />
              <div className="absolute top-full right-0 mt-2 p-3 bg-white rounded-xl shadow-xl border border-gray-100 z-50 min-w-[240px]">
                <p className="text-sm font-medium text-gray-700 mb-3">分享到</p>
                <ShareButtons
                  url={url}
                  title={title}
                  onShare={(platform) => {
                    onShare?.(platform);
                    setShowShareMenu(false);
                  }}
                  variant="pill"
                  size="md"
                  className="flex-wrap"
                />
              </div>
            </>
          )}
        </div>
      </div>
    </div>
  );
};

export default ShareButtons;

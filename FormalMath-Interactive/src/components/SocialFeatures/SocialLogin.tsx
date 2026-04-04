import React, { useState, useCallback } from 'react';
import { 
  Github, 
  Twitter, 
  Linkedin,
  MessageCircle,
  Chrome,
  Loader2,
  AlertCircle,
  CheckCircle2
} from 'lucide-react';

export type SocialProvider = 
  | 'github' 
  | 'google' 
  | 'twitter' 
  | 'linkedin' 
  | 'wechat' 
  | 'weibo'
  | 'apple';

export interface SocialLoginProps {
  onSuccess?: (user: SocialUser, provider: SocialProvider) => void;
  onError?: (error: SocialLoginError, provider: SocialProvider) => void;
  providers?: SocialProvider[];
  className?: string;
  disabled?: boolean;
}

export interface SocialUser {
  id: string;
  email: string;
  name: string;
  avatar?: string;
  provider: SocialProvider;
  accessToken: string;
  refreshToken?: string;
  expiresAt?: number;
  raw?: Record<string, unknown>;
}

export interface SocialLoginError {
  code: string;
  message: string;
  provider: SocialProvider;
}

interface ProviderConfig {
  id: SocialProvider;
  name: string;
  icon: React.ReactNode;
  color: string;
  bgColor: string;
  hoverBgColor: string;
  textColor: string;
  scopes: string[];
}

const providersConfig: ProviderConfig[] = [
  {
    id: 'github',
    name: 'GitHub',
    icon: <Github size={20} />,
    color: '#24292E',
    bgColor: 'bg-gray-900',
    hoverBgColor: 'hover:bg-gray-800',
    textColor: 'text-white',
    scopes: ['read:user', 'user:email'],
  },
  {
    id: 'google',
    name: 'Google',
    icon: <Chrome size={20} />,
    color: '#4285F4',
    bgColor: 'bg-white',
    hoverBgColor: 'hover:bg-gray-50',
    textColor: 'text-gray-700',
    scopes: ['openid', 'email', 'profile'],
  },
  {
    id: 'twitter',
    name: 'X / Twitter',
    icon: <Twitter size={20} />,
    color: '#000000',
    bgColor: 'bg-black',
    hoverBgColor: 'hover:bg-gray-900',
    textColor: 'text-white',
    scopes: ['tweet.read', 'users.read'],
  },
  {
    id: 'linkedin',
    name: 'LinkedIn',
    icon: <Linkedin size={20} />,
    color: '#0A66C2',
    bgColor: 'bg-[#0A66C2]',
    hoverBgColor: 'hover:bg-[#004182]',
    textColor: 'text-white',
    scopes: ['r_liteprofile', 'r_emailaddress'],
  },
  {
    id: 'wechat',
    name: '微信',
    icon: <MessageCircle size={20} />,
    color: '#07C160',
    bgColor: 'bg-[#07C160]',
    hoverBgColor: 'hover:bg-[#06ae56]',
    textColor: 'text-white',
    scopes: ['snsapi_userinfo'],
  },
  {
    id: 'weibo',
    name: '微博',
    icon: <MessageCircle size={20} />,
    color: '#E6162D',
    bgColor: 'bg-[#E6162D]',
    hoverBgColor: 'hover:bg-[#c91327]',
    textColor: 'text-white',
    scopes: ['email'],
  },
  {
    id: 'apple',
    name: 'Apple',
    icon: (
      <svg viewBox="0 0 24 24" className="w-5 h-5" fill="currentColor">
        <path d="M18.71 19.5c-.83 1.24-1.71 2.45-3.05 2.47-1.34.03-1.77-.79-3.29-.79-1.53 0-2 .77-3.27.82-1.31.05-2.3-1.32-3.14-2.53C4.25 17 2.94 12.45 4.7 9.39c.87-1.52 2.43-2.48 4.12-2.51 1.28-.02 2.5.87 3.29.87.78 0 2.26-1.07 3.81-.91.65.03 2.47.26 3.64 1.98-.09.06-2.17 1.28-2.15 3.81.03 3.02 2.65 4.03 2.68 4.04-.03.07-.42 1.44-1.38 2.83M13 3.5c.73-.83 1.94-1.46 2.94-1.5.13 1.17-.34 2.35-1.04 3.19-.69.85-1.83 1.51-2.95 1.42-.15-1.15.41-2.35 1.05-3.11z"/>
      </svg>
    ),
    color: '#000000',
    bgColor: 'bg-black',
    hoverBgColor: 'hover:bg-gray-900',
    textColor: 'text-white',
    scopes: ['name', 'email'],
  },
];

// OAuth 2.0 登录弹窗
const openOAuthPopup = (
  provider: SocialProvider,
  clientId: string,
  redirectUri: string,
  scopes: string[],
  state: string
): Window | null => {
  const width = 500;
  const height = 600;
  const left = (window.screen.width - width) / 2;
  const top = (window.screen.height - height) / 2;

  const oauthUrls: Record<SocialProvider, string> = {
    github: `https://github.com/login/oauth/authorize?client_id=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&scope=${scopes.join(',')}&state=${state}`,
    google: `https://accounts.google.com/o/oauth2/v2/auth?client_id=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${scopes.join(' ')}&state=${state}`,
    twitter: `https://twitter.com/i/oauth2/authorize?client_id=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${scopes.join(' ')}&state=${state}&code_challenge=challenge&code_challenge_method=plain`,
    linkedin: `https://www.linkedin.com/oauth/v2/authorization?client_id=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${scopes.join('%20')}&state=${state}`,
    wechat: `https://open.weixin.qq.com/connect/qrconnect?appid=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${scopes.join(',')}&state=${state}#wechat_redirect`,
    weibo: `https://api.weibo.com/oauth2/authorize?client_id=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${scopes.join(',')}&state=${state}`,
    apple: `https://appleid.apple.com/auth/authorize?client_id=${clientId}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${scopes.join('%20')}&state=${state}&response_mode=form_post`,
  };

  return window.open(
    oauthUrls[provider],
    `${provider}OAuth`,
    `width=${width},height=${height},left=${left},top=${top},toolbar=no,menubar=no,scrollbars=yes`
  );
};

export const SocialLogin: React.FC<SocialLoginProps> = ({
  onSuccess,
  onError,
  providers = ['github', 'google', 'twitter'],
  className = '',
  disabled = false,
}) => {
  const [loading, setLoading] = useState<SocialProvider | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [success, setSuccess] = useState<SocialProvider | null>(null);

  const availableProviders = providersConfig.filter(p => providers.includes(p.id));

  const handleLogin = useCallback(async (provider: ProviderConfig) => {
    if (loading || disabled) return;

    setLoading(provider.id);
    setError(null);
    setSuccess(null);

    try {
      // 从环境变量获取配置
      const clientId = import.meta.env[`VITE_${provider.id.toUpperCase()}_CLIENT_ID`];
      const redirectUri = `${window.location.origin}/auth/callback/${provider.id}`;
      const state = Math.random().toString(36).substring(7);

      if (!clientId) {
        // 模拟登录流程用于演示
        await new Promise(resolve => setTimeout(resolve, 1500));
        
        const mockUser: SocialUser = {
          id: `mock_${provider.id}_${Date.now()}`,
          email: `user@${provider.id}.com`,
          name: `${provider.name} User`,
          avatar: `https://api.dicebear.com/7.x/avataaars/svg?seed=${provider.id}`,
          provider: provider.id,
          accessToken: `mock_token_${Date.now()}`,
          expiresAt: Date.now() + 3600000,
        };

        setSuccess(provider.id);
        onSuccess?.(mockUser, provider.id);
        return;
      }

      // 打开 OAuth 弹窗
      const popup = openOAuthPopup(
        provider.id,
        clientId,
        redirectUri,
        provider.scopes,
        state
      );

      if (!popup) {
        throw new Error('无法打开登录窗口，请检查是否被浏览器阻止');
      }

      // 监听弹窗消息
      const handleMessage = (event: MessageEvent) => {
        if (event.origin !== window.location.origin) return;
        
        const { type, data, error: authError } = event.data;
        
        if (type === 'oauth:success') {
          const user: SocialUser = {
            id: data.id,
            email: data.email,
            name: data.name,
            avatar: data.avatar,
            provider: provider.id,
            accessToken: data.accessToken,
            refreshToken: data.refreshToken,
            expiresAt: data.expiresAt,
            raw: data.raw,
          };
          setSuccess(provider.id);
          onSuccess?.(user, provider.id);
        } else if (type === 'oauth:error') {
          const error: SocialLoginError = {
            code: authError.code || 'unknown',
            message: authError.message || '登录失败',
            provider: provider.id,
          };
          setError(error.message);
          onError?.(error, provider.id);
        }

        window.removeEventListener('message', handleMessage);
        popup.close();
        setLoading(null);
      };

      window.addEventListener('message', handleMessage);

      // 超时处理
      setTimeout(() => {
        window.removeEventListener('message', handleMessage);
        popup.close();
        setLoading(null);
      }, 120000);

    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : '登录失败';
      setError(errorMessage);
      onError?.({
        code: 'login_failed',
        message: errorMessage,
        provider: provider.id,
      }, provider.id);
      setLoading(null);
    }
  }, [loading, disabled, onSuccess, onError]);

  return (
    <div className={`space-y-4 ${className}`}>
      {error && (
        <div className="flex items-center gap-2 p-3 bg-red-50 border border-red-200 rounded-lg text-red-600 text-sm">
          <AlertCircle size={16} />
          <span>{error}</span>
        </div>
      )}

      {success && (
        <div className="flex items-center gap-2 p-3 bg-green-50 border border-green-200 rounded-lg text-green-600 text-sm">
          <CheckCircle2 size={16} />
          <span>登录成功！</span>
        </div>
      )}

      <div className="space-y-2">
        {availableProviders.map((provider) => (
          <button
            key={provider.id}
            onClick={() => handleLogin(provider)}
            disabled={disabled || loading !== null}
            className={`
              w-full flex items-center justify-center gap-3 px-4 py-3 
              rounded-lg font-medium transition-all duration-200
              ${provider.bgColor} ${provider.textColor} ${provider.hoverBgColor}
              ${disabled || loading ? 'opacity-50 cursor-not-allowed' : 'hover:shadow-md'}
              ${provider.id === 'google' ? 'border border-gray-300' : ''}
            `}
          >
            {loading === provider.id ? (
              <Loader2 size={20} className="animate-spin" />
            ) : (
              provider.icon
            )}
            <span>
              {loading === provider.id 
                ? '登录中...' 
                : `使用 ${provider.name} 登录`
              }
            </span>
          </button>
        ))}
      </div>

      <div className="relative">
        <div className="absolute inset-0 flex items-center">
          <div className="w-full border-t border-gray-200" />
        </div>
        <div className="relative flex justify-center text-sm">
          <span className="px-2 bg-white text-gray-500">或者</span>
        </div>
      </div>
    </div>
  );
};

// 社交账号绑定组件
export interface SocialLinkProps {
  linkedAccounts: SocialUser[];
  availableProviders?: SocialProvider[];
  onLink?: (user: SocialUser, provider: SocialProvider) => void;
  onUnlink?: (provider: SocialProvider) => void;
  className?: string;
}

export const SocialLink: React.FC<SocialLinkProps> = ({
  linkedAccounts,
  availableProviders = ['github', 'google', 'twitter'],
  onLink,
  onUnlink,
  className = '',
}) => {
  const linkedProviders = new Set(linkedAccounts.map(a => a.provider));
  const unlinkableProviders = providersConfig.filter(p => 
    availableProviders.includes(p.id) && linkedProviders.has(p.id)
  );
  const linkableProviders = providersConfig.filter(p => 
    availableProviders.includes(p.id) && !linkedProviders.has(p.id)
  );

  return (
    <div className={`space-y-4 ${className}`}>
      {/* 已绑定的账号 */}
      {unlinkableProviders.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 mb-2">已绑定账号</h4>
          <div className="space-y-2">
            {unlinkableProviders.map((provider) => {
              const account = linkedAccounts.find(a => a.provider === provider.id);
              return (
                <div
                  key={provider.id}
                  className="flex items-center justify-between p-3 bg-gray-50 rounded-lg"
                >
                  <div className="flex items-center gap-3">
                    <div 
                      className="w-10 h-10 rounded-full flex items-center justify-center text-white"
                      style={{ backgroundColor: provider.color }}
                    >
                      {provider.icon}
                    </div>
                    <div>
                      <p className="font-medium text-gray-800">{provider.name}</p>
                      <p className="text-sm text-gray-500">{account?.email}</p>
                    </div>
                  </div>
                  <button
                    onClick={() => onUnlink?.(provider.id)}
                    className="text-sm text-red-500 hover:text-red-600"
                  >
                    解绑
                  </button>
                </div>
              );
            })}
          </div>
        </div>
      )}

      {/* 可绑定的账号 */}
      {linkableProviders.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 mb-2">绑定更多账号</h4>
          <div className="grid grid-cols-2 gap-2">
            {linkableProviders.map((provider) => (
              <button
                key={provider.id}
                onClick={() => {/* 触发绑定流程 */}}
                className="flex items-center gap-2 p-3 border border-gray-200 rounded-lg hover:bg-gray-50 transition-colors"
              >
                <div 
                  className="w-8 h-8 rounded-full flex items-center justify-center text-white"
                  style={{ backgroundColor: provider.color }}
                >
                  {React.cloneElement(provider.icon as React.ReactElement, { size: 16 })}
                </div>
                <span className="text-sm font-medium text-gray-700">
                  绑定{provider.name}
                </span>
              </button>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

export default SocialLogin;

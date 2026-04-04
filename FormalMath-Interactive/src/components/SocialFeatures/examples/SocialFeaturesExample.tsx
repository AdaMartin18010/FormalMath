import React, { useState } from 'react';
import {
  ShareButtons,
  FloatingShareButton,
  InlineShareButtons,
  SocialShare,
  SocialLogin,
  SocialLink,
  ContentEmbed,
  OpenGraphMeta,
  useSocialMeta,
  useShareCount,
  generateConceptMeta,
} from '../';
import type { SocialUser, SocialProvider } from '../';

// 示例：完整的社交功能演示页面
export const SocialFeaturesExample: React.FC = () => {
  const [showShareModal, setShowShareModal] = useState(false);
  const [linkedAccounts, setLinkedAccounts] = useState<SocialUser[]>([]);
  const [isLiked, setIsLiked] = useState(false);
  const [isBookmarked, setIsBookmarked] = useState(false);

  const currentUrl = typeof window !== 'undefined' ? window.location.href : '';
  const title = '代数基础概念 - FormalMath';
  const description = '探索代数的基本概念、定理和应用，构建坚实的数学基础。';

  // 使用社交元数据 hook
  const { share } = useSocialMeta({
    title,
    description,
    url: currentUrl,
    image: 'https://formalmath.example.com/images/algebra.png',
    type: 'article',
    keywords: ['数学', '代数', 'FormalMath'],
    updateDocument: true,
  });

  // 获取分享计数
  const { counts, loading } = useShareCount(currentUrl, ['facebook']);

  // 生成概念元数据
  const conceptMeta = generateConceptMeta(
    {
      name: '代数',
      description: '代数的基本概念和定理',
      id: 'algebra-basics',
      category: '基础数学',
      image: '/images/algebra.png',
    },
    'https://formalmath.example.com'
  );

  const handleLoginSuccess = (user: SocialUser, provider: SocialProvider) => {
    console.log(`Logged in with ${provider}:`, user);
    alert(`成功使用 ${provider} 登录！欢迎 ${user.name}`);
  };

  const handleLoginError = (error: any, provider: SocialProvider) => {
    console.error(`Login error with ${provider}:`, error);
    alert(`登录失败: ${error.message}`);
  };

  const handleShare = (platform: string) => {
    console.log(`Shared to ${platform}`);
  };

  return (
    <div className="max-w-4xl mx-auto p-6 space-y-12">
      {/* Open Graph 元数据 */}
      <OpenGraphMeta {...conceptMeta} />

      {/* 页面标题 */}
      <header className="text-center">
        <h1 className="text-4xl font-bold text-gray-800 mb-4">
          社交媒体功能演示
        </h1>
        <p className="text-gray-600">
          展示 FormalMath 的社交分享、登录和嵌入功能
        </p>
      </header>

      {/* 1. 分享按钮组 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          1. 分享按钮组
        </h2>
        <p className="text-gray-600 mb-6">
          支持多种社交平台的分享按钮，可自定义样式和尺寸。
        </p>
        
        <div className="space-y-4">
          <div>
            <h3 className="text-sm font-medium text-gray-500 mb-2">默认样式</h3>
            <ShareButtons
              url={currentUrl}
              title={title}
              description={description}
              hashtags={['数学', '代数', 'FormalMath']}
              platforms={['twitter', 'facebook', 'linkedin', 'weibo', 'copy']}
              onShare={handleShare}
            />
          </div>

          <div>
            <h3 className="text-sm font-medium text-gray-500 mb-2">Pill 样式</h3>
            <ShareButtons
              url={currentUrl}
              title={title}
              platforms={['twitter', 'facebook', 'linkedin']}
              variant="pill"
              size="md"
            />
          </div>

          <div>
            <h3 className="text-sm font-medium text-gray-500 mb-2">Minimal 样式</h3>
            <ShareButtons
              url={currentUrl}
              title={title}
              platforms={['twitter', 'facebook', 'copy']}
              variant="minimal"
              size="sm"
            />
          </div>
        </div>
      </section>

      {/* 2. 内联分享按钮 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          2. 内联分享按钮（带统计）
        </h2>
        <p className="text-gray-600 mb-6">
          包含点赞、收藏、分享和浏览量统计的完整分享组件。
        </p>
        
        <InlineShareButtons
          url={currentUrl}
          title={title}
          likes={128}
          views={1024}
          bookmarks={32}
          isLiked={isLiked}
          isBookmarked={isBookmarked}
          onLike={() => setIsLiked(!isLiked)}
          onBookmark={() => setIsBookmarked(!isBookmarked)}
          onShare={handleShare}
        />
      </section>

      {/* 3. 分享弹窗 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          3. 分享弹窗
        </h2>
        <p className="text-gray-600 mb-6">
          完整的分享弹窗，支持二维码、嵌入代码等功能。
        </p>
        
        <button
          onClick={() => setShowShareModal(true)}
          className="px-6 py-3 bg-blue-500 hover:bg-blue-600 text-white font-medium rounded-lg transition-colors"
        >
          打开分享弹窗
        </button>

        {showShareModal && (
          <div className="fixed inset-0 z-50 flex items-center justify-center p-4 bg-black/50">
            <SocialShare
              data={{
                title,
                description,
                url: currentUrl,
                image: 'https://formalmath.example.com/images/algebra-preview.png',
              }}
              platforms={['wechat', 'weibo', 'twitter', 'facebook', 'linkedin', 'copy', 'qrcode']}
              onClose={() => setShowShareModal(false)}
              onShare={(platform) => console.log(`Shared to ${platform}`)}
            />
          </div>
        )}
      </section>

      {/* 4. 社交登录 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          4. 社交登录
        </h2>
        <p className="text-gray-600 mb-6">
          支持 GitHub、Google、Twitter、LinkedIn、微信、微博、Apple 等多种登录方式。
        </p>
        
        <div className="grid md:grid-cols-2 gap-6">
          <div>
            <h3 className="text-lg font-medium text-gray-700 mb-4">登录</h3>
            <SocialLogin
              providers={['github', 'google', 'twitter', 'linkedin', 'wechat', 'apple']}
              onSuccess={handleLoginSuccess}
              onError={handleLoginError}
            />
          </div>

          <div>
            <h3 className="text-lg font-medium text-gray-700 mb-4">账号绑定</h3>
            <SocialLink
              linkedAccounts={linkedAccounts}
              availableProviders={['github', 'google', 'twitter', 'linkedin']}
              onLink={(user) => setLinkedAccounts([...linkedAccounts, user])}
              onUnlink={(provider) => 
                setLinkedAccounts(linkedAccounts.filter(a => a.provider !== provider))
              }
            />
          </div>
        </div>
      </section>

      {/* 5. 内容嵌入 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          5. 内容嵌入
        </h2>
        <p className="text-gray-600 mb-6">
          生成 iframe 嵌入代码，支持响应式布局和自定义配置。
        </p>
        
        <ContentEmbed
          url="https://formalmath.example.com/concept/algebra"
          title="代数基础概念"
          description="代数的基本概念和定理"
          thumbnail="/images/algebra-thumb.png"
          config={{
            size: 'responsive',
            theme: 'auto',
            showHeader: true,
            allowFullscreen: true,
            borderRadius: 8,
          }}
        />
      </section>

      {/* 6. 分享计数 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          6. 分享计数
        </h2>
        <p className="text-gray-600 mb-6">
          获取内容在各社交平台的分享统计数据。
        </p>
        
        <div className="flex items-center gap-4">
          {loading ? (
            <span className="text-gray-500">加载中...</span>
          ) : (
            <>
              <div className="px-4 py-2 bg-blue-50 rounded-lg">
                <span className="text-sm text-gray-600">Facebook</span>
                <p className="text-2xl font-bold text-blue-600">
                  {counts.facebook || 0}
                </p>
              </div>
              <div className="px-4 py-2 bg-red-50 rounded-lg">
                <span className="text-sm text-gray-600">Pinterest</span>
                <p className="text-2xl font-bold text-red-600">
                  {counts.pinterest || 0}
                </p>
              </div>
            </>
          )}
        </div>
      </section>

      {/* 7. 预定义配置 */}
      <section className="bg-white rounded-xl shadow-lg p-6">
        <h2 className="text-2xl font-semibold text-gray-800 mb-4">
          7. 预定义配置
        </h2>
        <p className="text-gray-600 mb-6">
          使用预定义的元数据配置快速生成社交分享内容。
        </p>
        
        <div className="space-y-4">
          <div className="p-4 bg-gray-50 rounded-lg">
            <h3 className="font-medium text-gray-700">conceptMeta (生成)</h3>
            <pre className="mt-2 text-sm text-gray-600 overflow-x-auto">
              {JSON.stringify(conceptMeta, null, 2)}
            </pre>
          </div>
        </div>
      </section>

      {/* 浮动分享按钮 */}
      <FloatingShareButton
        url={currentUrl}
        title={title}
        description={description}
        hashtags={['数学', '代数']}
        position="bottom-right"
        offset={{ x: 24, y: 24 }}
        onShare={handleShare}
      />
    </div>
  );
};

export default SocialFeaturesExample;

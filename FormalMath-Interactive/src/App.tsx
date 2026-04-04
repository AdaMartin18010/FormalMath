import React, { Suspense, useState, useEffect } from 'react';
import { BrowserRouter as Router, Routes, Route, useNavigate, useLocation } from 'react-router-dom';
import { QueryClient, QueryClientProvider } from 'react-query';
import { HelmetProvider } from 'react-helmet-async';
import { Header } from '@components/Header';
import { Footer } from '@components/Footer';
import { PageLoading } from '@components/Loading';
import { SEOHead } from '@components/SEO';
import { ErrorBoundary } from '@components/ErrorHandling';
import { NetworkStatus } from '@components/ErrorHandling';
import { ToastContainer, useToast } from '@components/Feedback';
import { TourGuide, FeatureIntro } from '@components/Onboarding';
import { useOnboarding } from '@components/Onboarding';
import { MobileBottomNav } from '@mobile/MobileBottomNav';
import { MobileDrawer } from '@mobile/MobileDrawer';
import { PWAInstallPrompt } from '@mobile/PWAInstallPrompt';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';
import { useShakeDetection } from '@hooks/mobile/useMobileDetect';
import { useDarkMode } from '@hooks/mobile/useDarkMode';
import { initPerformanceMonitoring } from '@utils/performance';
import { preconnectDomain } from '@utils/seo';

// Lazy load pages for better performance
const Home = React.lazy(() => import('@pages/Home'));
const KnowledgeGraph = React.lazy(() => import('@pages/KnowledgeGraph'));
const ReasoningTree = React.lazy(() => import('@pages/ReasoningTree'));
const MindMap = React.lazy(() => import('@pages/MindMap'));
const Comparison = React.lazy(() => import('@pages/Comparison'));
const DecisionTree = React.lazy(() => import('@pages/DecisionTree'));
const Evolution = React.lazy(() => import('@pages/Evolution'));
const VisualizationGallery = React.lazy(() => import('@pages/VisualizationGallery'));
const Analytics = React.lazy(() => import('@pages/Analytics'));
const ProofAssistant = React.lazy(() => import('@pages/ProofAssistant'));
const Community = React.lazy(() => import('@pages/Community'));
const CommunityAdmin = React.lazy(() => import('@pages/Admin/CommunityAdmin'));
const Exercise = React.lazy(() => import('@pages/Exercise'));

// 创建 Query Client 带优化配置
const createQueryClient = () => new QueryClient({
  defaultOptions: {
    queries: {
      staleTime: 5 * 60 * 1000, // 5 minutes
      retry: (failureCount, error: any) => {
        // 网络错误时最多重试2次
        if (error?.message?.includes('network')) {
          return failureCount < 2;
        }
        return failureCount < 1;
      },
      refetchOnWindowFocus: false,
      cacheTime: 10 * 60 * 1000, // 10 minutes
    },
  },
});

// SEO预连接优化
const SEO_OPTIMIZATION = {
  preconnectDomains: [
    'https://fonts.googleapis.com',
    'https://fonts.gstatic.com',
  ],
};

// 导入 cn 工具函数
import { cn } from '@utils/classNames';

// 引导步骤配置
const tourSteps = [
  {
    id: 'welcome',
    title: '欢迎来到 FormalMath',
    description: '这是一个交互式数学可视化平台，帮助您以全新的方式探索数学知识。',
    icon: <span className="text-2xl">🎉</span>,
  },
  {
    id: 'knowledge-graph',
    title: '知识图谱',
    description: '探索数学概念之间的关联网络，发现隐藏的知识结构。',
    icon: <span className="text-2xl">🕸️</span>,
    target: '[href="/knowledge-graph"]',
  },
  {
    id: 'reasoning-tree',
    title: '推理树',
    description: '追踪数学证明的推理路径，理解逻辑链条。',
    icon: <span className="text-2xl">🌳</span>,
    target: '[href="/reasoning-tree"]',
  },
  {
    id: 'mobile',
    title: '移动端优化',
    description: '支持PWA安装，随时随地学习数学。支持手势操作和离线访问。',
    icon: <span className="text-2xl">📱</span>,
  },
];

// Layout wrapper for pages with header only
const SimpleLayout: React.FC<{ 
  children: React.ReactNode;
  isMobile: boolean;
}> = ({ children, isMobile }) => (
  <div className="min-h-screen flex flex-col bg-gray-50 dark:bg-slate-900 transition-colors">
    <Header />
    <main className={cn(
      "flex-1",
      isMobile && "pb-20" // 为底部导航栏留出空间
    )}>
      {children}
    </main>
    <Footer />
  </div>
);

// Layout for visualization pages (no footer to maximize space)
const VisualizationLayout: React.FC<{ 
  children: React.ReactNode;
  isMobile: boolean;
}> = ({ children, isMobile }) => (
  <div className="min-h-screen flex flex-col bg-white dark:bg-slate-900 transition-colors">
    <Header />
    <main className={cn(
      "flex-1",
      isMobile && "pb-20" // 为底部导航栏留出空间
    )}>
      {children}
    </main>
  </div>
);

// Main App Component
function App() {
  const { isMobile } = useMobileDetect();
  const { isDark } = useDarkMode();
  const [isDrawerOpen, setIsDrawerOpen] = useState(false);
  const [showTour, setShowTour] = useState(false);
  const [showFeatureIntro] = useState(true);
  const navigate = useNavigate();
  const location = useLocation();
  const { toasts, dismissToast, success, error } = useToast();
  const { shouldShowTour, completeTour, recordVisit } = useOnboarding();

  // 初始化性能监控
  useEffect(() => {
    initPerformanceMonitoring();
    SEO_OPTIMIZATION.preconnectDomains.forEach(domain => {
      preconnectDomain(domain, domain.includes('gstatic'));
    });
  }, []);

  // 移除初始加载器
  useEffect(() => {
    const loader = document.getElementById('initial-loader');
    if (loader) {
      loader.style.opacity = '0';
      setTimeout(() => loader.remove(), 300);
    }
  }, []);

  // 记录访问并检查是否显示引导
  useEffect(() => {
    recordVisit();
    if (shouldShowTour() && location.pathname === '/') {
      setShowTour(true);
    }
  }, [recordVisit, shouldShowTour, location.pathname]);

  // 注册 Service Worker
  useEffect(() => {
    if ('serviceWorker' in navigator) {
      navigator.serviceWorker
        .register('/sw.js')
        .then((registration) => {
          console.log('SW registered:', registration);
          success('应用已准备好离线使用');
        })
        .catch((err) => {
          console.log('SW registration failed:', err);
          error('离线功能初始化失败');
        });
    }
  }, [success, error]);

  // 摇一摇快捷操作 - 打开搜索
  useShakeDetection({
    onShake: () => {
      if (isMobile) {
        const searchButton = document.querySelector('[title="搜索"]') as HTMLButtonElement;
        searchButton?.click();
        success('摇一摇', '已打开搜索功能');
      }
    },
  });

  // 获取当前页面key
  const getPageKey = () => {
    const path = location.pathname.replace('/FormalMath', '').replace(/^\//, '');
    return path || 'home';
  };

  const handleTourComplete = () => {
    completeTour();
    setShowTour(false);
    success('完成引导', '您已完成新用户引导！');
  };

  return (
    <HelmetProvider>
      <QueryClientProvider client={createQueryClient()}>
        <ErrorBoundary onError={(err) => error('发生错误', err.message)}>
          {/* SEO Head 组件 */}
          <SEOHead pageKey={getPageKey()} />
          
          {/* 网络状态指示器 */}
          <NetworkStatus />
          
          {/* Toast 通知 */}
          <ToastContainer toasts={toasts} onDismiss={dismissToast} position="bottom-right" />
          
          {/* 用户引导 */}
          <TourGuide
            steps={tourSteps}
            isOpen={showTour}
            onClose={() => setShowTour(false)}
            onComplete={handleTourComplete}
          />
          
          <div className={cn(
            "min-h-screen transition-colors",
            isDark ? "dark bg-slate-900" : "bg-white"
          )}>
            <Routes>
              {/* Home Page */}
              <Route
                path="/"
                element={
                  <SimpleLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载首页" />}>
                      {showFeatureIntro && <FeatureIntro />}
                      <Home />
                    </Suspense>
                  </SimpleLayout>
                }
              />

              {/* Knowledge Graph Page */}
              <Route
                path="/knowledge-graph"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载知识图谱" />}>
                      <KnowledgeGraph />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* Reasoning Tree Page */}
              <Route
                path="/reasoning-tree"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载推理树" />}>
                      <ReasoningTree />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* Mind Map Page */}
              <Route
                path="/mind-map"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载思维导图" />}>
                      <MindMap />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* Comparison Page */}
              <Route
                path="/comparison"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载对比分析" />}>
                      <Comparison />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* Decision Tree Page */}
              <Route
                path="/decision-tree"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载决策树" />}>
                      <DecisionTree />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* Evolution Page */}
              <Route
                path="/evolution"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载演化历史" />}>
                      <Evolution />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* Analytics Dashboard Page */}
              <Route
                path="/analytics"
                element={
                  <SimpleLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载数据分析" />}>
                      <Analytics />
                    </Suspense>
                  </SimpleLayout>
                }
              />

              {/* Proof Assistant Page */}
              <Route
                path="/proof-assistant"
                element={
                  <SimpleLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载证明助手" />}>
                      <ProofAssistant />
                    </Suspense>
                  </SimpleLayout>
                }
              />

              {/* Community Page */}
              <Route
                path="/community"
                element={
                  <SimpleLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载学习社区" />}>
                      <Community />
                    </Suspense>
                  </SimpleLayout>
                }
              />

              {/* Community Admin Page */}
              <Route
                path="/admin/community"
                element={
                  <Suspense fallback={<PageLoading title="正在加载管理后台" />}>
                    <CommunityAdmin />
                  </Suspense>
                }
              />

              {/* Exercise Page */}
              <Route
                path="/exercise"
                element={
                  <SimpleLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载练习系统" />}>
                      <Exercise />
                    </Suspense>
                  </SimpleLayout>
                }
              />

              {/* Visualization Gallery Page */}
              <Route
                path="/visualization-gallery"
                element={
                  <VisualizationLayout isMobile={isMobile}>
                    <Suspense fallback={<PageLoading title="正在加载可视化组件库" />}>
                      <VisualizationGallery />
                    </Suspense>
                  </VisualizationLayout>
                }
              />

              {/* 404 Page */}
              <Route
                path="*"
                element={
                  <SimpleLayout isMobile={isMobile}>
                    <div className="min-h-[60vh] flex items-center justify-center px-4">
                      <div className="text-center">
                        <h1 className="text-6xl font-bold text-gray-300 dark:text-slate-700 mb-4">404</h1>
                        <h2 className="text-2xl font-semibold text-gray-700 dark:text-gray-300 mb-2">页面未找到</h2>
                        <p className="text-gray-500 dark:text-gray-400 mb-6">您访问的页面不存在或已被移除</p>
                        <a
                          href="/"
                          className="inline-flex items-center gap-2 px-6 py-3 bg-blue-600 text-white font-medium rounded-xl hover:bg-blue-700 transition-colors"
                        >
                          返回首页
                        </a>
                      </div>
                    </div>
                  </SimpleLayout>
                }
              />
            </Routes>

            {/* 移动端底部导航 */}
            {isMobile && (
              <>
                <MobileBottomNav onMoreClick={() => setIsDrawerOpen(true)} />
                <MobileDrawer
                  isOpen={isDrawerOpen}
                  onClose={() => setIsDrawerOpen(false)}
                  onNavigate={(path) => navigate(path)}
                />
              </>
            )}

            {/* PWA 安装提示 */}
            <PWAInstallPrompt delay={5000} />
          </div>
        </ErrorBoundary>
      </QueryClientProvider>
    </HelmetProvider>
  );
}

// 包装 Router
function AppWithRouter() {
  return (
    <Router basename="/FormalMath">
      <App />
    </Router>
  );
}

export default AppWithRouter;

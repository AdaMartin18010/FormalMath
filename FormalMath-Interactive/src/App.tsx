import React, { Suspense, useState, useEffect } from 'react';
import { BrowserRouter as Router, Routes, Route, useNavigate, useLocation } from 'react-router-dom';
import { QueryClient, QueryClientProvider } from 'react-query';
import { HelmetProvider } from 'react-helmet-async';
import { Header } from '@components/Header';
import { Footer } from '@components/Footer';
import { PageLoading } from '@components/Loading';
import { SEOHead } from '@components/SEO';
import { MobileBottomNav } from '@mobile/MobileBottomNav';
import { MobileDrawer } from '@mobile/MobileDrawer';
import { PWAInstallPrompt } from '@mobile/PWAInstallPrompt';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';
import { useShakeDetection } from '@hooks/mobile/useMobileDetect';
import { useDarkMode } from '@hooks/mobile/useDarkMode';
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

// Create Query Client with mobile optimizations
const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      staleTime: 5 * 60 * 1000, // 5 minutes
      retry: 2,
      refetchOnWindowFocus: false,
      // 移动端优化：网络不佳时延长缓存时间
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

// Error Boundary Component
class ErrorBoundary extends React.Component<
  { children: React.ReactNode },
  { hasError: boolean; error: Error | null }
> {
  constructor(props: { children: React.ReactNode }) {
    super(props);
    this.state = { hasError: false, error: null };
  }

  static getDerivedStateFromError(error: Error) {
    return { hasError: true, error };
  }

  componentDidCatch(error: Error, errorInfo: React.ErrorInfo) {
    console.error('Error caught by boundary:', error, errorInfo);
  }

  render() {
    if (this.state.hasError) {
      return (
        <div className="min-h-screen flex items-center justify-center bg-gray-50 dark:bg-slate-900">
          <div className="text-center p-8 bg-white dark:bg-slate-800 rounded-2xl shadow-lg max-w-md mx-4">
            <div className="w-16 h-16 bg-red-100 dark:bg-red-900/30 rounded-full flex items-center justify-center mx-auto mb-4">
              <svg className="w-8 h-8 text-red-600 dark:text-red-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
              </svg>
            </div>
            <h2 className="text-xl font-bold text-gray-900 dark:text-white mb-2">出错了</h2>
            <p className="text-gray-600 dark:text-gray-400 mb-4">
              {this.state.error?.message || '应用程序遇到了意外错误'}
            </p>
            <button
              onClick={() => window.location.reload()}
              className="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
            >
              刷新页面
            </button>
          </div>
        </div>
      );
    }

    return this.props.children;
  }
}

// 导入 cn 工具函数
import { cn } from '@utils/classNames';

// Main App Component
function App() {
  const { isMobile } = useMobileDetect();
  const { isDark } = useDarkMode();
  const [isDrawerOpen, setIsDrawerOpen] = useState(false);
  const navigate = useNavigate();
  const location = useLocation();

  // SEO预连接优化
  useEffect(() => {
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

  // 注册 Service Worker
  useEffect(() => {
    if ('serviceWorker' in navigator) {
      navigator.serviceWorker
        .register('/sw.js')
        .then((registration) => {
          console.log('SW registered:', registration);
        })
        .catch((error) => {
          console.log('SW registration failed:', error);
        });
    }
  }, []);

  // 摇一摇快捷操作 - 打开搜索
  useShakeDetection({
    onShake: () => {
      if (isMobile) {
        // 触发搜索功能
        const searchButton = document.querySelector('[title="搜索"]') as HTMLButtonElement;
        searchButton?.click();
      }
    },
  });

  // 获取当前页面key
  const getPageKey = () => {
    const path = location.pathname.replace('/FormalMath', '').replace(/^\//, '');
    return path || 'home';
  };

  return (
    <HelmetProvider>
    <QueryClientProvider client={queryClient}>
      <ErrorBoundary>
        {/* SEO Head 组件 */}
        <SEOHead pageKey={getPageKey()} />
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

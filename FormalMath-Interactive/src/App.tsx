import React, { Suspense } from 'react';
import { BrowserRouter as Router, Routes, Route } from 'react-router-dom';
import { QueryClient, QueryClientProvider } from 'react-query';
import { Header } from '@components/Header';
import { Footer } from '@components/Footer';
import { Loading, PageLoading } from '@components/Loading';

// Lazy load pages for better performance
const Home = React.lazy(() => import('@pages/Home'));
const KnowledgeGraph = React.lazy(() => import('@pages/KnowledgeGraph'));
const ReasoningTree = React.lazy(() => import('@pages/ReasoningTree'));
const MindMap = React.lazy(() => import('@pages/MindMap'));
const Comparison = React.lazy(() => import('@pages/Comparison'));
const DecisionTree = React.lazy(() => import('@pages/DecisionTree'));
const Evolution = React.lazy(() => import('@pages/Evolution'));

// Create Query Client
const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      staleTime: 5 * 60 * 1000, // 5 minutes
      retry: 2,
      refetchOnWindowFocus: false,
    },
  },
});

// Layout wrapper for pages with header only
const SimpleLayout: React.FC<{ children: React.ReactNode }> = ({ children }) => (
  <div className="min-h-screen flex flex-col bg-gray-50">
    <Header />
    <main className="flex-1">
      {children}
    </main>
    <Footer />
  </div>
);

// Layout for visualization pages (no footer to maximize space)
const VisualizationLayout: React.FC<{ children: React.ReactNode }> = ({ children }) => (
  <div className="min-h-screen flex flex-col bg-white">
    <Header />
    {children}
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
        <div className="min-h-screen flex items-center justify-center bg-gray-50">
          <div className="text-center p-8 bg-white rounded-2xl shadow-lg max-w-md">
            <div className="w-16 h-16 bg-red-100 rounded-full flex items-center justify-center mx-auto mb-4">
              <svg className="w-8 h-8 text-red-600" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
              </svg>
            </div>
            <h2 className="text-xl font-bold text-gray-900 mb-2">出错了</h2>
            <p className="text-gray-600 mb-4">
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

function App() {
  return (
    <QueryClientProvider client={queryClient}>
      <ErrorBoundary>
        <Router>
          <Routes>
            {/* Home Page */}
            <Route
              path="/"
              element={
                <SimpleLayout>
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
                <VisualizationLayout>
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
                <VisualizationLayout>
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
                <VisualizationLayout>
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
                <VisualizationLayout>
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
                <VisualizationLayout>
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
                <VisualizationLayout>
                  <Suspense fallback={<PageLoading title="正在加载演化历史" />}>
                    <Evolution />
                  </Suspense>
                </VisualizationLayout>
              }
            />

            {/* 404 Page */}
            <Route
              path="*"
              element={
                <SimpleLayout>
                  <div className="min-h-[60vh] flex items-center justify-center">
                    <div className="text-center">
                      <h1 className="text-6xl font-bold text-gray-300 mb-4">404</h1>
                      <h2 className="text-2xl font-semibold text-gray-700 mb-2">页面未找到</h2>
                      <p className="text-gray-500 mb-6">您访问的页面不存在或已被移除</p>
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
        </Router>
      </ErrorBoundary>
    </QueryClientProvider>
  );
}

export default App;

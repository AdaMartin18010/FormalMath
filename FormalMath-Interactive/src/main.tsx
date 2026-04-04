import React from 'react';
import ReactDOM from 'react-dom/client';
import { registerSW } from 'virtual:pwa-register';
import App from './App';
import './index.css';
import { initPerformanceMonitoring } from '@utils/performance';

// 初始化性能监控（尽可能早）
initPerformanceMonitoring();

// 注册 Service Worker
const updateSW = registerSW({
  onNeedRefresh() {
    // 有新版本可用
    if (confirm('检测到新版本，是否刷新页面以更新？')) {
      updateSW(true);
    }
  },
  onOfflineReady() {
    console.log('应用已准备好离线使用');
    // 可以在这里显示一个提示
  },
  onRegistered(r) {
    console.log('SW Registered:', r);
  },
  onRegisterError(error) {
    console.log('SW registration error', error);
  },
});

// 渲染应用
ReactDOM.createRoot(document.getElementById('root')!).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>
);

// 性能监控 - 页面加载完成
if ('performance' in window) {
  window.addEventListener('load', () => {
    // 使用 requestIdleCallback 延迟执行非关键性能分析
    if ('requestIdleCallback' in window) {
      requestIdleCallback(() => {
        const perfData = performance.getEntriesByType('navigation')[0] as PerformanceNavigationTiming;
        if (perfData) {
          const metrics = {
            loadTime: perfData.loadEventEnd - perfData.startTime,
            domContentLoaded: perfData.domContentLoadedEventEnd - perfData.startTime,
            firstPaint: perfData.responseEnd - perfData.startTime,
          };
          console.log('页面性能指标:', metrics);
          
          // 发送到分析服务
          if ('gtag' in window) {
            (window as any).gtag('event', 'page_performance', {
              event_category: 'Performance',
              ...metrics,
            });
          }
        }
      });
    }
  });
}

// 错误监控
window.addEventListener('error', (event) => {
  console.error('全局错误:', event.error);
  
  // 发送到分析服务
  if ('gtag' in window) {
    (window as any).gtag('event', 'exception', {
      description: event.error?.message || 'Unknown error',
      fatal: true,
    });
  }
});

// 未处理的 Promise 错误
window.addEventListener('unhandledrejection', (event) => {
  console.error('未处理的 Promise 错误:', event.reason);
  
  if ('gtag' in window) {
    (window as any).gtag('event', 'exception', {
      description: `Unhandled Promise: ${event.reason}`,
      fatal: false,
    });
  }
});

// 在线/离线状态检测
window.addEventListener('online', () => {
  console.log('网络已恢复');
  document.body.classList.remove('offline');
});

window.addEventListener('offline', () => {
  console.log('网络已断开');
  document.body.classList.add('offline');
});

// 初始化离线状态
if (!navigator.onLine) {
  document.body.classList.add('offline');
}

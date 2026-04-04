import React from 'react';
import ReactDOM from 'react-dom/client';
import { registerSW } from 'virtual:pwa-register';
import App from './App';
import './index.css';

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

// 性能监控
if ('performance' in window) {
  window.addEventListener('load', () => {
    // 发送性能指标（如果需要）
    setTimeout(() => {
      const perfData = performance.getEntriesByType('navigation')[0] as PerformanceNavigationTiming;
      if (perfData) {
        console.log('页面加载时间:', perfData.loadEventEnd - perfData.startTime, 'ms');
      }
    }, 0);
  });
}

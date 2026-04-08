const CACHE_NAME = 'cognitive-diagnosis-v1';
const STATIC_ASSETS = [
  '/',
  '/index.html',
  '/static/js/main.chunk.js',
  '/static/js/bundle.js',
  '/static/css/main.chunk.css'
];

// 安装时缓存静态资源
self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME)
      .then((cache) => {
        console.log('缓存静态资源');
        return cache.addAll(STATIC_ASSETS);
      })
      .catch((err) => {
        console.error('缓存失败:', err);
      })
  );
  self.skipWaiting();
});

// 激活时清理旧缓存
self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((cacheNames) => {
      return Promise.all(
        cacheNames
          .filter((name) => name !== CACHE_NAME)
          .map((name) => caches.delete(name))
      );
    })
  );
  self.clients.claim();
});

// 拦截请求并提供缓存
self.addEventListener('fetch', (event) => {
  // 跳过非GET请求和Chrome扩展请求
  if (event.request.method !== 'GET' || 
      event.request.url.startsWith('chrome-extension')) {
    return;
  }

  event.respondWith(
    caches.match(event.request).then((response) => {
      // 返回缓存或发起网络请求
      if (response) {
        // 后台更新缓存
        fetch(event.request)
          .then((networkResponse) => {
            if (networkResponse && networkResponse.status === 200) {
              caches.open(CACHE_NAME).then((cache) => {
                cache.put(event.request, networkResponse.clone());
              });
            }
          })
          .catch(() => {});
        return response;
      }

      return fetch(event.request)
        .then((networkResponse) => {
          // 缓存新请求
          if (networkResponse && networkResponse.status === 200) {
            const responseToCache = networkResponse.clone();
            caches.open(CACHE_NAME).then((cache) => {
              cache.put(event.request, responseToCache);
            });
          }
          return networkResponse;
        })
        .catch(() => {
          // 离线时返回离线页面
          if (event.request.mode === 'navigate') {
            return caches.match('/index.html');
          }
          return new Response('离线模式 - 请检查网络连接', {
            status: 503,
            statusText: 'Service Unavailable',
            headers: new Headers({
              'Content-Type': 'text/plain;charset=UTF-8'
            })
          });
        });
    })
  );
});

// 处理后台同步
self.addEventListener('sync', (event) => {
  if (event.tag === 'sync-diagnosis-data') {
    event.waitUntil(syncDiagnosisData());
  }
});

async function syncDiagnosisData() {
  // 同步离线诊断数据
  console.log('同步诊断数据...');
}

// 推送通知
self.addEventListener('push', (event) => {
  const options = {
    body: event.data?.text() || '您有新的诊断报告',
    icon: '/logo192.png',
    badge: '/logo192.png',
    tag: 'diagnosis-notification',
    requireInteraction: true,
    actions: [
      { action: 'view', title: '查看' },
      { action: 'close', title: '关闭' }
    ]
  };
  
  event.waitUntil(
    self.registration.showNotification('FormalMath认知诊断', options)
  );
});

// 通知点击处理
self.addEventListener('notificationclick', (event) => {
  event.notification.close();
  
  if (event.action === 'view') {
    event.waitUntil(
      clients.openWindow('/reports')
    );
  }
});

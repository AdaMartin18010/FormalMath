import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import { VitePWA } from 'vite-plugin-pwa'
import path from 'path'

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [
    react({
      // 优化 React 编译
      babel: {
        plugins: [
          ['@babel/plugin-transform-react-jsx', { runtime: 'automatic' }],
        ],
      },
    }),
    VitePWA({
      registerType: 'autoUpdate',
      includeAssets: ['favicon.ico', 'apple-touch-icon.png', 'masked-icon.svg'],
      manifest: {
        name: 'FormalMath Interactive - 交互式数学可视化平台',
        short_name: 'FormalMath',
        description: 'FormalMath是一个现代化的数学知识图谱可视化平台，提供交互式数学概念探索、推理树可视化、证明助手等功能，助力数学学习与教学。',
        theme_color: '#2563eb',
        background_color: '#ffffff',
        display: 'standalone',
        scope: '/FormalMath/',
        start_url: '/FormalMath/',
        orientation: 'portrait-primary',
        icons: [
          {
            src: '/FormalMath/icons/icon-72x72.png',
            sizes: '72x72',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-96x96.png',
            sizes: '96x96',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-128x128.png',
            sizes: '128x128',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-144x144.png',
            sizes: '144x144',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-152x152.png',
            sizes: '152x152',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-192x192.png',
            sizes: '192x192',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-384x384.png',
            sizes: '384x384',
            type: 'image/png',
            purpose: 'maskable any'
          },
          {
            src: '/FormalMath/icons/icon-512x512.png',
            sizes: '512x512',
            type: 'image/png',
            purpose: 'maskable any'
          }
        ],
        categories: ['education', 'productivity'],
        lang: 'zh-CN',
        dir: 'ltr',
        shortcuts: [
          {
            name: '知识图谱',
            short_name: '图谱',
            description: '快速打开知识图谱',
            url: '/FormalMath/knowledge-graph',
            icons: [{ src: '/FormalMath/icons/graph-96x96.png', sizes: '96x96' }]
          },
          {
            name: '推理树',
            short_name: '推理',
            description: '快速打开推理树',
            url: '/FormalMath/reasoning-tree',
            icons: [{ src: '/FormalMath/icons/tree-96x96.png', sizes: '96x96' }]
          },
          {
            name: '思维导图',
            short_name: '导图',
            description: '快速打开思维导图',
            url: '/FormalMath/mind-map',
            icons: [{ src: '/FormalMath/icons/mindmap-96x96.png', sizes: '96x96' }]
          }
        ],
        related_applications: [],
        prefer_related_applications: false
      },
      workbox: {
        globPatterns: ['**/*.{js,css,html,ico,png,svg,woff2}'],
        runtimeCaching: [
          {
            urlPattern: /^https:\/\/fonts\.googleapis\.com\/.*/i,
            handler: 'CacheFirst',
            options: {
              cacheName: 'google-fonts-cache',
              expiration: {
                maxEntries: 10,
                maxAgeSeconds: 60 * 60 * 24 * 365 // 1 year
              },
              cacheableResponse: {
                statuses: [0, 200]
              }
            }
          },
          {
            urlPattern: /^https:\/\/fonts\.gstatic\.com\/.*/i,
            handler: 'CacheFirst',
            options: {
              cacheName: 'google-fonts-cache',
              expiration: {
                maxEntries: 10,
                maxAgeSeconds: 60 * 60 * 24 * 365 // 1 year
              },
              cacheableResponse: {
                statuses: [0, 200]
              }
            }
          },
          {
            urlPattern: /\.(?:png|jpg|jpeg|svg|gif|webp)$/i,
            handler: 'CacheFirst',
            options: {
              cacheName: 'images-cache',
              expiration: {
                maxEntries: 100,
                maxAgeSeconds: 60 * 60 * 24 * 30 // 30 days
              }
            }
          },
          {
            urlPattern: /\.(?:js|css)$/i,
            handler: 'StaleWhileRevalidate',
            options: {
              cacheName: 'static-resources',
              expiration: {
                maxEntries: 100,
                maxAgeSeconds: 60 * 60 * 24 * 7 // 7 days
              }
            }
          },
          {
            urlPattern: /^https:\/\/api\./i,
            handler: 'NetworkFirst',
            options: {
              cacheName: 'api-cache',
              expiration: {
                maxEntries: 200,
                maxAgeSeconds: 60 * 60 * 24 // 24 hours
              },
              networkTimeoutSeconds: 10
            }
          }
        ],
        skipWaiting: true,
        clientsClaim: true,
        cleanupOutdatedCaches: true,
        // 预缓存策略优化
        navigateFallback: '/index.html',
        navigateFallbackDenylist: [/^\/api/, /^\/admin/],
      },
      devOptions: {
        enabled: true,
        type: 'module'
      }
    })
  ],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
      '@components': path.resolve(__dirname, './src/components'),
      '@pages': path.resolve(__dirname, './src/pages'),
      '@hooks': path.resolve(__dirname, './src/hooks'),
      '@utils': path.resolve(__dirname, './src/utils'),
      '@types': path.resolve(__dirname, './src/types'),
      '@visualizations': path.resolve(__dirname, './src/visualizations'),
      '@mobile': path.resolve(__dirname, './src/mobile'),
      '@stores': path.resolve(__dirname, './src/stores'),
      '@config': path.resolve(__dirname, './src/config'),
    },
  },
  build: {
    outDir: 'dist',
    sourcemap: true,
    rollupOptions: {
      external: ['framer-motion'],
      output: {
        manualChunks: {
          // 核心框架
          'vendor-core': ['react', 'react-dom'],
          'vendor-router': ['react-router-dom', 'react-helmet-async'],
          
          // 状态管理与数据获取
          'vendor-state': ['zustand', 'react-query'],
          
          // 可视化库
          'vendor-d3': ['d3', 'd3-selection', 'd3-scale', 'd3-hierarchy', 'd3-force-3d'],
          'vendor-three': ['three', '@react-three/fiber', '@react-three/drei'],
          'vendor-mermaid': ['mermaid'],
          
          // 工具库
          'vendor-utils': ['axios', 'clsx', 'tailwind-merge'],
          'vendor-markdown': ['react-markdown', 'rehype-katex', 'remark-math'],
          'vendor-icons': ['lucide-react'],
          
          // 编辑器与协作
          'vendor-collab': ['yjs', 'y-websocket', 'y-protocols'],
          
          // 数学渲染
          'vendor-math': ['katex'],
          'vendor-syntax': ['react-syntax-highlighter'],
        },
        assetFileNames: (assetInfo) => {
          const info = assetInfo.name.split('.')
          const ext = info[info.length - 1]
          if (/\.(png|jpe?g|gif|svg|webp|ico)$/i.test(assetInfo.name)) {
            return 'assets/images/[name]-[hash][extname]'
          }
          if (/\.(woff2?|ttf|otf|eot)$/i.test(assetInfo.name)) {
            return 'assets/fonts/[name]-[hash][extname]'
          }
          if (/\.(css)$/i.test(assetInfo.name)) {
            return 'assets/css/[name]-[hash][extname]'
          }
          return 'assets/[name]-[hash][extname]'
        },
        chunkFileNames: 'assets/js/[name]-[hash].js',
        entryFileNames: 'assets/js/[name]-[hash].js',
        
        // 优化 chunk 加载
        inlineDynamicImports: false,
        
        // 控制 chunk 大小
        experimentalMinChunkSize: 20000,
      },
    },
    target: 'es2020',
    minify: 'terser',
    terserOptions: {
      compress: {
        drop_console: true,
        drop_debugger: true,
        pure_funcs: ['console.log', 'console.info', 'console.debug'],
        passes: 2,
      },
      mangle: {
        safari10: true,
      },
      format: {
        comments: false,
      },
    },
    reportCompressedSize: true,
    chunkSizeWarningLimit: 1000,
    
    // CSS 优化
    cssMinify: true,
    cssCodeSplit: true,
    
    // 资源内联阈值
    assetsInlineLimit: 4096,
    
    // 模块预加载
    modulePreload: {
      polyfill: true,
    },
  },
  base: '/FormalMath/',
  server: {
    port: 3000,
    host: true,
    open: true,
    proxy: {
      '/api': {
        target: 'http://localhost:8000',
        changeOrigin: true,
        rewrite: (path) => path.replace(/^\/api/, ''),
      },
    },
    // 启用压缩
    fs: {
      strict: true,
    },
  },
  preview: {
    port: 4173,
    host: true,
  },
  css: {
    devSourcemap: true,
    // PostCSS 配置已在单独文件中
  },
  optimizeDeps: {
    include: [
      'react',
      'react-dom',
      'react-router-dom',
      'd3',
      'mermaid',
      'zustand',
      'react-query',
      'lucide-react',
    ],
    exclude: ['framer-motion'],
    // 强制预构建
    force: true,
  },
  
  // 实验性功能
  experimental: {
    // 启用 renderBuiltUrl 以支持 CDN
    renderBuiltUrl(filename, { hostType }) {
      if (hostType === 'js') {
        return { relative: true }
      }
      return { relative: true }
    },
  },
  
  // 依赖优化
  json: {
    stringify: true,
  },
  
  // 构建时清除 console
  esbuild: {
    drop: process.env.NODE_ENV === 'production' ? ['console', 'debugger'] : [],
  },
})
